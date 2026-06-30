// Lean compiler output
// Module: Lake.Util.OrderedTagAttribute
// Imports: Lean.Attributes
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_Attribute_Builtin_ensureNoArgs,
    l_Lean_instBEqAttributeKind_beq, l_Lean_instInhabitedAttributeImpl_default,
    l_Lean_registerBuiltinAttribute, runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_quickLt;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg, l_Lean_instInhabitedEnvExtension_default,
    l_Lean_instInhabitedPersistentEnvExtensionState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
pub static l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116, 96,
        32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
    ],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instInhabitedOrderedTagAttribute_default___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instInhabitedOrderedTagAttribute_default___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedOrderedTagAttribute_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedOrderedTagAttribute: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__3_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
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
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__3_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__5_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__6_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
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
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__6_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__8_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__10_value:
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
    m_data: [101, 120, 97, 99, 116, 0],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__10_value)
            as *mut leanh::LeanObject,
        14997215300048349804 as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__14_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__15_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__14_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__15_value)
            as *mut leanh::LeanObject,
        7677164612348466033 as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__17_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_registerOrderedTagAttribute___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__0_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        116, 97, 103, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__3_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 108, 111, 99, 97, 108, 32, 101, 110, 116,
        114, 105, 101, 115, 58, 32, 0,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___lam__6___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0],
};
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__6___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___lam__6___closed__2_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__6___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_registerOrderedTagAttribute___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_registerOrderedTagAttribute___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__1_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_registerOrderedTagAttribute___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_registerOrderedTagAttribute___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__2_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_registerOrderedTagAttribute___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_registerOrderedTagAttribute___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__3_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_registerOrderedTagAttribute___lam__3 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_registerOrderedTagAttribute___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__4_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_registerOrderedTagAttribute___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__5_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_registerOrderedTagAttribute___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__6_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_registerOrderedTagAttribute___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_registerOrderedTagAttribute___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lake_OrderedTagAttribute_hasTag___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_OrderedTagAttribute_hasTag___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_OrderedTagAttribute_getAllEntries___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_OrderedTagAttribute_getAllEntries___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__0(
    mut v_x_647_: *mut leanh::LeanObject,
    mut v___y_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1;
    v___x_651_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_651_, 0, v___x_650_);
    return v___x_651_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___boxed(
    mut v_x_652_: *mut leanh::LeanObject,
    mut v___y_653_: *mut leanh::LeanObject,
    mut v___y_654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_655_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__0(v_x_652_, v___y_653_);
    leanh::lean_dec_ref(v___y_653_);
    leanh::lean_dec_ref(v_x_652_);
    return v_res_655_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__1(
    mut v_s_656_: *mut leanh::LeanObject,
    mut v_x_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_s_656_);
    return v_s_656_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__1___boxed(
    mut v_s_658_: *mut leanh::LeanObject,
    mut v_x_659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__1(v_s_658_, v_x_659_);
    leanh::lean_dec(v_x_659_);
    leanh::lean_dec_ref(v_s_658_);
    return v_res_660_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(
    mut v_x_665_: *mut leanh::LeanObject,
    mut v_x_666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_667_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1;
    return v___x_667_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed(
    mut v_x_668_: *mut leanh::LeanObject,
    mut v_x_669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(v_x_668_, v_x_669_);
    leanh::lean_dec_ref(v_x_669_);
    leanh::lean_dec_ref(v_x_668_);
    return v_res_670_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(
    mut v_x_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_672_ = leanh::lean_box(0);
    return v___x_672_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__3___boxed(
    mut v_x_673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(v_x_673_);
    leanh::lean_dec_ref(v_x_673_);
    return v_res_674_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = l_Lean_instInhabitedEnvExtension_default(leanh::lean_box(0));
    return v___x_679_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__5()
-> *mut leanh::LeanObject {
    let mut v___f_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_680_ = l_Lake_instInhabitedOrderedTagAttribute_default___closed__3;
    v___f_681_ = l_Lake_instInhabitedOrderedTagAttribute_default___closed__2;
    v___f_682_ = l_Lake_instInhabitedOrderedTagAttribute_default___closed__1;
    v___f_683_ = l_Lake_instInhabitedOrderedTagAttribute_default___closed__0;
    v___x_684_ = leanh::lean_box(0);
    v___x_685_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__4_once),
        _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__4,
    );
    v___x_686_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_686_, 0, v___x_685_);
    leanh::lean_ctor_set(v___x_686_, 1, v___x_684_);
    leanh::lean_ctor_set(v___x_686_, 2, v___f_683_);
    leanh::lean_ctor_set(v___x_686_, 3, v___f_682_);
    leanh::lean_ctor_set(v___x_686_, 4, v___f_681_);
    leanh::lean_ctor_set(v___x_686_, 5, v___f_680_);
    return v___x_686_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_687_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__5_once),
        _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__5,
    );
    v___x_688_ = l_Lean_instInhabitedAttributeImpl_default;
    v___x_689_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_689_, 0, v___x_688_);
    leanh::lean_ctor_set(v___x_689_, 1, v___x_687_);
    return v___x_689_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute_default()
-> *mut leanh::LeanObject {
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_690_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__6),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__6_once),
        _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__6,
    );
    return v___x_690_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute() -> *mut leanh::LeanObject {
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lake_instInhabitedOrderedTagAttribute_default;
    return v___x_691_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_718_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__10;
    v___x_719_ = l_Lean_mkAtom(v___x_718_);
    return v___x_719_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__12_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__12,
    );
    v___x_721_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_722_ = lean_array_push(v___x_721_, v___x_720_);
    return v___x_722_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__17;
    v___x_732_ = l_Lean_mkAtom(v___x_731_);
    return v___x_732_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__18_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__18,
    );
    v___x_734_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_735_ = lean_array_push(v___x_734_, v___x_733_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__19_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__19,
    );
    v___x_737_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__16;
    v___x_738_ = leanh::lean_box(2);
    v___x_739_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_739_, 0, v___x_738_);
    leanh::lean_ctor_set(v___x_739_, 1, v___x_737_);
    leanh::lean_ctor_set(v___x_739_, 2, v___x_736_);
    return v___x_739_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__20_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__20,
    );
    v___x_741_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__13_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__13,
    );
    v___x_742_ = lean_array_push(v___x_741_, v___x_740_);
    return v___x_742_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_743_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__21_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__21,
    );
    v___x_744_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__11;
    v___x_745_ = leanh::lean_box(2);
    v___x_746_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_746_, 0, v___x_745_);
    leanh::lean_ctor_set(v___x_746_, 1, v___x_744_);
    leanh::lean_ctor_set(v___x_746_, 2, v___x_743_);
    return v___x_746_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_747_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__22_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__22,
    );
    v___x_748_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_749_ = lean_array_push(v___x_748_, v___x_747_);
    return v___x_749_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_750_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__23_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__23,
    );
    v___x_751_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__9;
    v___x_752_ = leanh::lean_box(2);
    v___x_753_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_753_, 0, v___x_752_);
    leanh::lean_ctor_set(v___x_753_, 1, v___x_751_);
    leanh::lean_ctor_set(v___x_753_, 2, v___x_750_);
    return v___x_753_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_754_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__24_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__24,
    );
    v___x_755_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_756_ = lean_array_push(v___x_755_, v___x_754_);
    return v___x_756_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_757_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__25_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__25,
    );
    v___x_758_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__7;
    v___x_759_ = leanh::lean_box(2);
    v___x_760_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_760_, 0, v___x_759_);
    leanh::lean_ctor_set(v___x_760_, 1, v___x_758_);
    leanh::lean_ctor_set(v___x_760_, 2, v___x_757_);
    return v___x_760_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__26_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__26,
    );
    v___x_762_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_763_ = lean_array_push(v___x_762_, v___x_761_);
    return v___x_763_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__27_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__27,
    );
    v___x_765_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__4;
    v___x_766_ = leanh::lean_box(2);
    v___x_767_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_767_, 0, v___x_766_);
    leanh::lean_ctor_set(v___x_767_, 1, v___x_765_);
    leanh::lean_ctor_set(v___x_767_, 2, v___x_764_);
    return v___x_767_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1() -> *mut leanh::LeanObject
{
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__28_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__28,
    );
    return v___x_768_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__0(
    mut v_es_769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_es_769_);
    return v_es_769_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__0___boxed(
    mut v_es_770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_771_ = l_Lake_registerOrderedTagAttribute___lam__0(v_es_770_);
    leanh::lean_dec_ref(v_es_770_);
    return v_res_771_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__1(
    mut v_s_784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_785_ = l_Lake_registerOrderedTagAttribute___lam__1___closed__5;
    v___x_786_ = lean_array_get_size(v_s_784_);
    v___x_787_ = l_Nat_reprFast(v___x_786_);
    v___x_788_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_788_, 0, v___x_787_);
    v___x_789_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_789_, 0, v___x_785_);
    leanh::lean_ctor_set(v___x_789_, 1, v___x_788_);
    return v___x_789_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__1___boxed(
    mut v_s_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Lake_registerOrderedTagAttribute___lam__1(v_s_790_);
    leanh::lean_dec_ref(v_s_790_);
    return v_res_791_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__2(
    mut v_x_792_: *mut leanh::LeanObject,
    mut v_s_793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_s_793_, 2);
    v___x_794_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_794_, 0, v_s_793_);
    leanh::lean_ctor_set(v___x_794_, 1, v_s_793_);
    leanh::lean_ctor_set(v___x_794_, 2, v_s_793_);
    return v___x_794_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__2___boxed(
    mut v_x_795_: *mut leanh::LeanObject,
    mut v_s_796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_797_ = l_Lake_registerOrderedTagAttribute___lam__2(v_x_795_, v_s_796_);
    leanh::lean_dec_ref(v_x_795_);
    return v_res_797_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__3(
    mut v_s_798_: *mut leanh::LeanObject,
    mut v_n_799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_800_ = lean_array_push(v_s_798_, v_n_799_);
    return v___x_800_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__4(
    mut v___x_801_: *mut leanh::LeanObject,
    mut v_x_802_: *mut leanh::LeanObject,
    mut v_x_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_805_, 0, v___x_801_);
    return v___x_805_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__4___boxed(
    mut v___x_806_: *mut leanh::LeanObject,
    mut v_x_807_: *mut leanh::LeanObject,
    mut v_x_808_: *mut leanh::LeanObject,
    mut v___y_809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_810_ = l_Lake_registerOrderedTagAttribute___lam__4(v___x_806_, v_x_807_, v_x_808_);
    leanh::lean_dec_ref(v_x_808_);
    leanh::lean_dec_ref(v_x_807_);
    return v_res_810_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__5(
    mut v___x_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_813_, 0, v___x_811_);
    return v___x_813_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__5___boxed(
    mut v___x_814_: *mut leanh::LeanObject,
    mut v___y_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lake_registerOrderedTagAttribute___lam__5(v___x_814_);
    return v_res_816_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_817_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0);
    v___x_819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_819_, 0, v___x_818_);
    return v___x_819_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_820_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
    v___x_821_ = leanh::lean_unsigned_to_nat(0);
    v___x_822_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_822_, 0, v___x_821_);
    leanh::lean_ctor_set(v___x_822_, 1, v___x_821_);
    leanh::lean_ctor_set(v___x_822_, 2, v___x_821_);
    leanh::lean_ctor_set(v___x_822_, 3, v___x_821_);
    leanh::lean_ctor_set(v___x_822_, 4, v___x_820_);
    leanh::lean_ctor_set(v___x_822_, 5, v___x_820_);
    leanh::lean_ctor_set(v___x_822_, 6, v___x_820_);
    leanh::lean_ctor_set(v___x_822_, 7, v___x_820_);
    leanh::lean_ctor_set(v___x_822_, 8, v___x_820_);
    leanh::lean_ctor_set(v___x_822_, 9, v___x_820_);
    return v___x_822_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = leanh::lean_unsigned_to_nat(32);
    v___x_824_ = lean_mk_empty_array_with_capacity(v___x_823_);
    v___x_825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_825_, 0, v___x_824_);
    return v___x_825_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_826_: usize = 0;
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = 5usize;
    v___x_827_ = leanh::lean_unsigned_to_nat(0);
    v___x_828_ = leanh::lean_unsigned_to_nat(32);
    v___x_829_ = lean_mk_empty_array_with_capacity(v___x_828_);
    v___x_830_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3);
    v___x_831_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_831_, 0, v___x_830_);
    leanh::lean_ctor_set(v___x_831_, 1, v___x_829_);
    leanh::lean_ctor_set(v___x_831_, 2, v___x_827_);
    leanh::lean_ctor_set(v___x_831_, 3, v___x_827_);
    leanh::lean_ctor_set_usize(v___x_831_, 4, v___x_826_);
    return v___x_831_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = leanh::lean_box(1);
    v___x_833_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4);
    v___x_834_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
    v___x_835_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_835_, 0, v___x_834_);
    leanh::lean_ctor_set(v___x_835_, 1, v___x_833_);
    leanh::lean_ctor_set(v___x_835_, 2, v___x_832_);
    return v___x_835_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(
    mut v_msgData_836_: *mut leanh::LeanObject,
    mut v___y_837_: *mut leanh::LeanObject,
    mut v___y_838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_840_ = lean_st_ref_get(v___y_838_);
    v_env_841_ = leanh::lean_ctor_get(v___x_840_, 0);
    leanh::lean_inc_ref(v_env_841_);
    leanh::lean_dec(v___x_840_);
    v_options_842_ = leanh::lean_ctor_get(v___y_837_, 2);
    v___x_843_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2);
    v___x_844_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_842_);
    v___x_845_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_845_, 0, v_env_841_);
    leanh::lean_ctor_set(v___x_845_, 1, v___x_843_);
    leanh::lean_ctor_set(v___x_845_, 2, v___x_844_);
    leanh::lean_ctor_set(v___x_845_, 3, v_options_842_);
    v___x_846_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_846_, 0, v___x_845_);
    leanh::lean_ctor_set(v___x_846_, 1, v_msgData_836_);
    v___x_847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_847_, 0, v___x_846_);
    return v___x_847_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___boxed(
    mut v_msgData_848_: *mut leanh::LeanObject,
    mut v___y_849_: *mut leanh::LeanObject,
    mut v___y_850_: *mut leanh::LeanObject,
    mut v___y_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msgData_848_, v___y_849_, v___y_850_);
    leanh::lean_dec(v___y_850_);
    leanh::lean_dec_ref(v___y_849_);
    return v_res_852_;
}
pub unsafe fn l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
    mut v_msg_853_: *mut leanh::LeanObject,
    mut v___y_854_: *mut leanh::LeanObject,
    mut v___y_855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_862_: u8 = 0;
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_857_ = leanh::lean_ctor_get(v___y_854_, 5);
                v___x_858_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msg_853_, v___y_854_, v___y_855_);
                v_a_859_ = leanh::lean_ctor_get(v___x_858_, 0);
                v_isSharedCheck_867_ = (!leanh::lean_is_exclusive(v___x_858_)) as u8;
                if v_isSharedCheck_867_ == 0 {
                    v___x_861_ = v___x_858_;
                    v_isShared_862_ = v_isSharedCheck_867_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_859_);
                    leanh::lean_dec(v___x_858_);
                    v___x_861_ = leanh::lean_box(0);
                    v_isShared_862_ = v_isSharedCheck_867_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_857_);
                v___x_863_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_863_, 0, v_ref_857_);
                leanh::lean_ctor_set(v___x_863_, 1, v_a_859_);
                if v_isShared_862_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_861_, 1);
                    leanh::lean_ctor_set(v___x_861_, 0, v___x_863_);
                    v___x_865_ = v___x_861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_866_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
                    v___x_865_ = v_reuseFailAlloc_866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg___boxed(
    mut v_msg_868_: *mut leanh::LeanObject,
    mut v___y_869_: *mut leanh::LeanObject,
    mut v___y_870_: *mut leanh::LeanObject,
    mut v___y_871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_872_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
        v_msg_868_, v___y_869_, v___y_870_,
    );
    leanh::lean_dec(v___y_870_);
    leanh::lean_dec_ref(v___y_869_);
    return v_res_872_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Lake_registerOrderedTagAttribute___lam__6___closed__0;
    v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
    return v___x_875_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = l_Lake_registerOrderedTagAttribute___lam__6___closed__2;
    v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
    return v___x_878_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__6(
    mut v_name_879_: *mut leanh::LeanObject,
    mut v_decl_880_: *mut leanh::LeanObject,
    mut v___y_881_: *mut leanh::LeanObject,
    mut v___y_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_884_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__6___closed__1),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__6___closed__1_once),
        _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__1,
    );
    v___x_885_ = l_Lean_MessageData_ofName(v_name_879_);
    v___x_886_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_886_, 0, v___x_884_);
    leanh::lean_ctor_set(v___x_886_, 1, v___x_885_);
    v___x_887_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__6___closed__3),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__6___closed__3_once),
        _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__3,
    );
    v___x_888_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_888_, 0, v___x_886_);
    leanh::lean_ctor_set(v___x_888_, 1, v___x_887_);
    v___x_889_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
        v___x_888_, v___y_881_, v___y_882_,
    );
    return v___x_889_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__6___boxed(
    mut v_name_890_: *mut leanh::LeanObject,
    mut v_decl_891_: *mut leanh::LeanObject,
    mut v___y_892_: *mut leanh::LeanObject,
    mut v___y_893_: *mut leanh::LeanObject,
    mut v___y_894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lake_registerOrderedTagAttribute___lam__6(
        v_name_890_,
        v_decl_891_,
        v___y_892_,
        v___y_893_,
    );
    leanh::lean_dec(v___y_893_);
    leanh::lean_dec_ref(v___y_892_);
    leanh::lean_dec(v_decl_891_);
    return v_res_895_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_897_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0;
    v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
    return v___x_898_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_900_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2;
    v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
    return v___x_901_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4;
    v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
    return v___x_904_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(
    mut v_name_908_: *mut leanh::LeanObject,
    mut v_kind_909_: u8,
    mut v___y_910_: *mut leanh::LeanObject,
    mut v___y_911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_913_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1);
                v___x_914_ = l_Lean_MessageData_ofName(v_name_908_);
                v___x_915_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_915_, 0, v___x_913_);
                leanh::lean_ctor_set(v___x_915_, 1, v___x_914_);
                v___x_916_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3);
                v___x_917_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_917_, 0, v___x_915_);
                leanh::lean_ctor_set(v___x_917_, 1, v___x_916_);
                match v_kind_909_ {
                    0 => {
                        v___x_926_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6;
                        v___y_919_ = v___x_926_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_927_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7;
                        v___y_919_ = v___x_927_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_928_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8;
                        v___y_919_ = v___x_928_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_919_);
                v___x_920_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_920_, 0, v___y_919_);
                v___x_921_ = l_Lean_MessageData_ofFormat(v___x_920_);
                v___x_922_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_922_, 0, v___x_917_);
                leanh::lean_ctor_set(v___x_922_, 1, v___x_921_);
                v___x_923_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5);
                v___x_924_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_924_, 0, v___x_922_);
                leanh::lean_ctor_set(v___x_924_, 1, v___x_923_);
                v___x_925_ =
                    l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
                        v___x_924_, v___y_910_, v___y_911_,
                    );
                return v___x_925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___boxed(
    mut v_name_929_: *mut leanh::LeanObject,
    mut v_kind_930_: *mut leanh::LeanObject,
    mut v___y_931_: *mut leanh::LeanObject,
    mut v___y_932_: *mut leanh::LeanObject,
    mut v___y_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_934_: u8 = 0;
    let mut v_res_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_934_ = (leanh::lean_unbox(v_kind_930_) as u8);
    v_res_935_ =
        l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(
            v_name_929_,
            v_kind_boxed_934_,
            v___y_931_,
            v___y_932_,
        );
    leanh::lean_dec(v___y_932_);
    leanh::lean_dec_ref(v___y_931_);
    return v_res_935_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_937_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0;
    v___x_938_ = l_Lean_stringToMessageData(v___x_937_);
    return v___x_938_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2;
    v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
    return v___x_941_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4;
    v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
    return v___x_944_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(
    mut v_attrName_945_: *mut leanh::LeanObject,
    mut v_declName_946_: *mut leanh::LeanObject,
    mut v___y_947_: *mut leanh::LeanObject,
    mut v___y_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_950_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1);
    v___x_951_ = l_Lean_MessageData_ofName(v_attrName_945_);
    v___x_952_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_952_, 0, v___x_950_);
    leanh::lean_ctor_set(v___x_952_, 1, v___x_951_);
    v___x_953_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3);
    v___x_954_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_954_, 0, v___x_952_);
    leanh::lean_ctor_set(v___x_954_, 1, v___x_953_);
    v___x_955_ = 0;
    v___x_956_ = l_Lean_MessageData_ofConstName(v_declName_946_, v___x_955_);
    v___x_957_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_957_, 0, v___x_954_);
    leanh::lean_ctor_set(v___x_957_, 1, v___x_956_);
    v___x_958_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5);
    v___x_959_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_959_, 0, v___x_957_);
    leanh::lean_ctor_set(v___x_959_, 1, v___x_958_);
    v___x_960_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
        v___x_959_, v___y_947_, v___y_948_,
    );
    return v___x_960_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___boxed(
    mut v_attrName_961_: *mut leanh::LeanObject,
    mut v_declName_962_: *mut leanh::LeanObject,
    mut v___y_963_: *mut leanh::LeanObject,
    mut v___y_964_: *mut leanh::LeanObject,
    mut v___y_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_961_, v_declName_962_, v___y_963_, v___y_964_);
    leanh::lean_dec(v___y_964_);
    leanh::lean_dec_ref(v___y_963_);
    return v_res_966_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_967_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_968_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__7___closed__0),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__7___closed__0_once),
        _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__0,
    );
    v___x_969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_969_, 0, v___x_968_);
    return v___x_969_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__7___closed__1),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__7___closed__1_once),
        _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__1,
    );
    v___x_971_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_971_, 0, v___x_970_);
    leanh::lean_ctor_set(v___x_971_, 1, v___x_970_);
    return v___x_971_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__7(
    mut v_validate_972_: *mut leanh::LeanObject,
    mut v_a_973_: *mut leanh::LeanObject,
    mut v_name_974_: *mut leanh::LeanObject,
    mut v_decl_975_: *mut leanh::LeanObject,
    mut v_stx_976_: *mut leanh::LeanObject,
    mut v_kind_977_: u8,
    mut v___y_978_: *mut leanh::LeanObject,
    mut v___y_979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_987_: u8 = 0;
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1000_: u8 = 0;
    let mut v_asyncMode_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1013_: u8 = 0;
    let mut v_unused_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1015_: u8 = 0;
    let mut v_unused_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: u8 = 0;
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1024_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_976_, v___y_978_, v___y_979_);
                if leanh::lean_obj_tag(v___x_1024_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1024_, 1);
                    v___x_1025_ = 0;
                    v___x_1026_ = l_Lean_instBEqAttributeKind_beq(v_kind_977_, v___x_1025_);
                    if v___x_1026_ == 0 {
                        leanh::lean_dec(v_decl_975_);
                        leanh::lean_dec_ref(v_a_973_);
                        leanh::lean_dec_ref(v_validate_972_);
                        v___x_1027_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_974_, v_kind_977_, v___y_978_, v___y_979_);
                        return v___x_1027_;
                    } else {
                        v___y_1018_ = v___y_978_;
                        v___y_1019_ = v___y_979_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_decl_975_);
                    leanh::lean_dec(v_name_974_);
                    leanh::lean_dec_ref(v_a_973_);
                    leanh::lean_dec_ref(v_validate_972_);
                    return v___x_1024_;
                }
            }
            1 => {
                leanh::lean_inc(v___y_983_);
                leanh::lean_inc_ref(v___y_982_);
                leanh::lean_inc(v_decl_975_);
                v___x_984_ = leanh::lean_apply_4(
                    v_validate_972_,
                    v_decl_975_,
                    v___y_982_,
                    v___y_983_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_984_) == 0 {
                    v_isSharedCheck_1015_ = (!leanh::lean_is_exclusive(v___x_984_)) as u8;
                    if v_isSharedCheck_1015_ == 0 {
                        v_unused_1016_ = leanh::lean_ctor_get(v___x_984_, 0);
                        leanh::lean_dec(v_unused_1016_);
                        v___x_986_ = v___x_984_;
                        v_isShared_987_ = v_isSharedCheck_1015_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_984_);
                        v___x_986_ = leanh::lean_box(0);
                        v_isShared_987_ = v_isSharedCheck_1015_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_decl_975_);
                    leanh::lean_dec_ref(v_a_973_);
                    return v___x_984_;
                }
            }
            2 => {
                v___x_988_ = lean_st_ref_take(v___y_983_);
                v_toEnvExtension_989_ = leanh::lean_ctor_get(v_a_973_, 0);
                v_env_990_ = leanh::lean_ctor_get(v___x_988_, 0);
                v_nextMacroScope_991_ = leanh::lean_ctor_get(v___x_988_, 1);
                v_ngen_992_ = leanh::lean_ctor_get(v___x_988_, 2);
                v_auxDeclNGen_993_ = leanh::lean_ctor_get(v___x_988_, 3);
                v_traceState_994_ = leanh::lean_ctor_get(v___x_988_, 4);
                v_messages_995_ = leanh::lean_ctor_get(v___x_988_, 6);
                v_infoState_996_ = leanh::lean_ctor_get(v___x_988_, 7);
                v_snapshotTasks_997_ = leanh::lean_ctor_get(v___x_988_, 8);
                v_isSharedCheck_1013_ = (!leanh::lean_is_exclusive(v___x_988_)) as u8;
                if v_isSharedCheck_1013_ == 0 {
                    v_unused_1014_ = leanh::lean_ctor_get(v___x_988_, 5);
                    leanh::lean_dec(v_unused_1014_);
                    v___x_999_ = v___x_988_;
                    v_isShared_1000_ = v_isSharedCheck_1013_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_997_);
                    leanh::lean_inc(v_infoState_996_);
                    leanh::lean_inc(v_messages_995_);
                    leanh::lean_inc(v_traceState_994_);
                    leanh::lean_inc(v_auxDeclNGen_993_);
                    leanh::lean_inc(v_ngen_992_);
                    leanh::lean_inc(v_nextMacroScope_991_);
                    leanh::lean_inc(v_env_990_);
                    leanh::lean_dec(v___x_988_);
                    v___x_999_ = leanh::lean_box(0);
                    v_isShared_1000_ = v_isSharedCheck_1013_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_asyncMode_1001_ = leanh::lean_ctor_get(v_toEnvExtension_989_, 2);
                leanh::lean_inc(v_asyncMode_1001_);
                v___x_1002_ = leanh::lean_box(0);
                v___x_1003_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_a_973_,
                    v_env_990_,
                    v_decl_975_,
                    v_asyncMode_1001_,
                    v___x_1002_,
                );
                leanh::lean_dec(v_asyncMode_1001_);
                v___x_1004_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lake_registerOrderedTagAttribute___lam__7___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lake_registerOrderedTagAttribute___lam__7___closed__2_once
                    ),
                    _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__2,
                );
                if v_isShared_1000_ == 0 {
                    leanh::lean_ctor_set(v___x_999_, 5, v___x_1004_);
                    leanh::lean_ctor_set(v___x_999_, 0, v___x_1003_);
                    v___x_1006_ = v___x_999_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1012_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_nextMacroScope_991_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_ngen_992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_auxDeclNGen_993_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_traceState_994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 5, v___x_1004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 6, v_messages_995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 7, v_infoState_996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1012_, 8, v_snapshotTasks_997_);
                    v___x_1006_ = v_reuseFailAlloc_1012_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1007_ = lean_st_ref_set(v___y_983_, v___x_1006_);
                v___x_1008_ = leanh::lean_box(0);
                if v_isShared_987_ == 0 {
                    leanh::lean_ctor_set(v___x_986_, 0, v___x_1008_);
                    v___x_1010_ = v___x_986_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
                    v___x_1010_ = v_reuseFailAlloc_1011_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1010_;
            }
            6 => {
                v___x_1020_ = lean_st_ref_get(v___y_1019_);
                v_env_1021_ = leanh::lean_ctor_get(v___x_1020_, 0);
                leanh::lean_inc_ref(v_env_1021_);
                leanh::lean_dec(v___x_1020_);
                v___x_1022_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1021_, v_decl_975_);
                leanh::lean_dec_ref(v_env_1021_);
                if leanh::lean_obj_tag(v___x_1022_) == 0 {
                    leanh::lean_dec(v_name_974_);
                    v___y_982_ = v___y_1018_;
                    v___y_983_ = v___y_1019_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_1022_, 1);
                    leanh::lean_dec_ref(v_a_973_);
                    leanh::lean_dec_ref(v_validate_972_);
                    v___x_1023_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_name_974_, v_decl_975_, v___y_1018_, v___y_1019_);
                    return v___x_1023_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__7___boxed(
    mut v_validate_1028_: *mut leanh::LeanObject,
    mut v_a_1029_: *mut leanh::LeanObject,
    mut v_name_1030_: *mut leanh::LeanObject,
    mut v_decl_1031_: *mut leanh::LeanObject,
    mut v_stx_1032_: *mut leanh::LeanObject,
    mut v_kind_1033_: *mut leanh::LeanObject,
    mut v___y_1034_: *mut leanh::LeanObject,
    mut v___y_1035_: *mut leanh::LeanObject,
    mut v___y_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_1037_: u8 = 0;
    let mut v_res_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1037_ = (leanh::lean_unbox(v_kind_1033_) as u8);
    v_res_1038_ = l_Lake_registerOrderedTagAttribute___lam__7(
        v_validate_1028_,
        v_a_1029_,
        v_name_1030_,
        v_decl_1031_,
        v_stx_1032_,
        v_kind_boxed_1037_,
        v___y_1034_,
        v___y_1035_,
    );
    leanh::lean_dec(v___y_1035_);
    leanh::lean_dec_ref(v___y_1034_);
    return v_res_1038_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute(
    mut v_name_1049_: *mut leanh::LeanObject,
    mut v_descr_1050_: *mut leanh::LeanObject,
    mut v_validate_1051_: *mut leanh::LeanObject,
    mut v_ref_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut v_unused_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1084_: u8 = 0;
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1088_: u8 = 0;
    let mut v_a_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1092_: u8 = 0;
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1054_ = l_Lake_registerOrderedTagAttribute___closed__0;
                v___f_1055_ = l_Lake_registerOrderedTagAttribute___closed__1;
                v___f_1056_ = l_Lake_registerOrderedTagAttribute___closed__2;
                v___f_1057_ = l_Lake_registerOrderedTagAttribute___closed__3;
                v___f_1058_ = l_Lake_registerOrderedTagAttribute___closed__5;
                v___f_1059_ = l_Lake_registerOrderedTagAttribute___closed__6;
                v___x_1060_ = leanh::lean_box(2);
                v___x_1061_ = leanh::lean_box(0);
                leanh::lean_inc(v_ref_1052_);
                v___x_1062_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                leanh::lean_ctor_set(v___x_1062_, 0, v_ref_1052_);
                leanh::lean_ctor_set(v___x_1062_, 1, v___f_1059_);
                leanh::lean_ctor_set(v___x_1062_, 2, v___f_1058_);
                leanh::lean_ctor_set(v___x_1062_, 3, v___f_1057_);
                leanh::lean_ctor_set(v___x_1062_, 4, v___f_1056_);
                leanh::lean_ctor_set(v___x_1062_, 5, v___f_1055_);
                leanh::lean_ctor_set(v___x_1062_, 6, v___x_1060_);
                leanh::lean_ctor_set(v___x_1062_, 7, v___x_1061_);
                v___x_1063_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1063_, 0, v___x_1062_);
                leanh::lean_ctor_set(v___x_1063_, 1, v___f_1054_);
                v___x_1064_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1063_);
                if leanh::lean_obj_tag(v___x_1064_) == 0 {
                    v_a_1065_ = leanh::lean_ctor_get(v___x_1064_, 0);
                    leanh::lean_inc_n(v_a_1065_, 2);
                    leanh::lean_dec_ref_known(v___x_1064_, 1);
                    leanh::lean_inc_n(v_name_1049_, 2);
                    v___f_1066_ = leanh::lean_alloc_closure(
                        l_Lake_registerOrderedTagAttribute___lam__6___boxed
                            as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1066_, 0, v_name_1049_);
                    v___f_1067_ = leanh::lean_alloc_closure(
                        l_Lake_registerOrderedTagAttribute___lam__7___boxed
                            as *mut core::ffi::c_void,
                        9,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1067_, 0, v_validate_1051_);
                    leanh::lean_closure_set(v___f_1067_, 1, v_a_1065_);
                    leanh::lean_closure_set(v___f_1067_, 2, v_name_1049_);
                    v___x_1068_ = 0;
                    v___x_1069_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v___x_1069_, 0, v_ref_1052_);
                    leanh::lean_ctor_set(v___x_1069_, 1, v_name_1049_);
                    leanh::lean_ctor_set(v___x_1069_, 2, v_descr_1050_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1069_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_1068_,
                    );
                    v___x_1070_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1070_, 0, v___x_1069_);
                    leanh::lean_ctor_set(v___x_1070_, 1, v___f_1067_);
                    leanh::lean_ctor_set(v___x_1070_, 2, v___f_1066_);
                    leanh::lean_inc_ref(v___x_1070_);
                    v___x_1071_ = l_Lean_registerBuiltinAttribute(v___x_1070_);
                    if leanh::lean_obj_tag(v___x_1071_) == 0 {
                        v_isSharedCheck_1079_ =
                            (!leanh::lean_is_exclusive(v___x_1071_)) as u8;
                        if v_isSharedCheck_1079_ == 0 {
                            v_unused_1080_ = leanh::lean_ctor_get(v___x_1071_, 0);
                            leanh::lean_dec(v_unused_1080_);
                            v___x_1073_ = v___x_1071_;
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1071_);
                            v___x_1073_ = leanh::lean_box(0);
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_1070_, 3);
                        leanh::lean_dec(v_a_1065_);
                        v_a_1081_ = leanh::lean_ctor_get(v___x_1071_, 0);
                        v_isSharedCheck_1088_ =
                            (!leanh::lean_is_exclusive(v___x_1071_)) as u8;
                        if v_isSharedCheck_1088_ == 0 {
                            v___x_1083_ = v___x_1071_;
                            v_isShared_1084_ = v_isSharedCheck_1088_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1081_);
                            leanh::lean_dec(v___x_1071_);
                            v___x_1083_ = leanh::lean_box(0);
                            v_isShared_1084_ = v_isSharedCheck_1088_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_ref_1052_);
                    leanh::lean_dec_ref(v_validate_1051_);
                    leanh::lean_dec_ref(v_descr_1050_);
                    leanh::lean_dec(v_name_1049_);
                    v_a_1089_ = leanh::lean_ctor_get(v___x_1064_, 0);
                    v_isSharedCheck_1096_ = (!leanh::lean_is_exclusive(v___x_1064_)) as u8;
                    if v_isSharedCheck_1096_ == 0 {
                        v___x_1091_ = v___x_1064_;
                        v_isShared_1092_ = v_isSharedCheck_1096_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1089_);
                        leanh::lean_dec(v___x_1064_);
                        v___x_1091_ = leanh::lean_box(0);
                        v_isShared_1092_ = v_isSharedCheck_1096_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1075_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1075_, 0, v___x_1070_);
                leanh::lean_ctor_set(v___x_1075_, 1, v_a_1065_);
                if v_isShared_1074_ == 0 {
                    leanh::lean_ctor_set(v___x_1073_, 0, v___x_1075_);
                    v___x_1077_ = v___x_1073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1078_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
                    v___x_1077_ = v_reuseFailAlloc_1078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1077_;
            }
            3 => {
                if v_isShared_1084_ == 0 {
                    v___x_1086_ = v___x_1083_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1087_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
                    v___x_1086_ = v_reuseFailAlloc_1087_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1086_;
            }
            5 => {
                if v_isShared_1092_ == 0 {
                    v___x_1094_ = v___x_1091_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
                    v___x_1094_ = v_reuseFailAlloc_1095_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___boxed(
    mut v_name_1097_: *mut leanh::LeanObject,
    mut v_descr_1098_: *mut leanh::LeanObject,
    mut v_validate_1099_: *mut leanh::LeanObject,
    mut v_ref_1100_: *mut leanh::LeanObject,
    mut v_a_1101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1102_ = l_Lake_registerOrderedTagAttribute(
        v_name_1097_,
        v_descr_1098_,
        v_validate_1099_,
        v_ref_1100_,
    );
    return v_res_1102_;
}
pub unsafe fn l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(
    mut v_00_u03b1_1103_: *mut leanh::LeanObject,
    mut v_msg_1104_: *mut leanh::LeanObject,
    mut v___y_1105_: *mut leanh::LeanObject,
    mut v___y_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1108_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
        v_msg_1104_,
        v___y_1105_,
        v___y_1106_,
    );
    return v___x_1108_;
}
pub unsafe fn l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___boxed(
    mut v_00_u03b1_1109_: *mut leanh::LeanObject,
    mut v_msg_1110_: *mut leanh::LeanObject,
    mut v___y_1111_: *mut leanh::LeanObject,
    mut v___y_1112_: *mut leanh::LeanObject,
    mut v___y_1113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1114_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(
        v_00_u03b1_1109_,
        v_msg_1110_,
        v___y_1111_,
        v___y_1112_,
    );
    leanh::lean_dec(v___y_1112_);
    leanh::lean_dec_ref(v___y_1111_);
    return v_res_1114_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(
    mut v_00_u03b1_1115_: *mut leanh::LeanObject,
    mut v_attrName_1116_: *mut leanh::LeanObject,
    mut v_declName_1117_: *mut leanh::LeanObject,
    mut v___y_1118_: *mut leanh::LeanObject,
    mut v___y_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_1116_, v_declName_1117_, v___y_1118_, v___y_1119_);
    return v___x_1121_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___boxed(
    mut v_00_u03b1_1122_: *mut leanh::LeanObject,
    mut v_attrName_1123_: *mut leanh::LeanObject,
    mut v_declName_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
    mut v___y_1126_: *mut leanh::LeanObject,
    mut v___y_1127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1128_ =
        l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(
            v_00_u03b1_1122_,
            v_attrName_1123_,
            v_declName_1124_,
            v___y_1125_,
            v___y_1126_,
        );
    leanh::lean_dec(v___y_1126_);
    leanh::lean_dec_ref(v___y_1125_);
    return v_res_1128_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(
    mut v_00_u03b1_1129_: *mut leanh::LeanObject,
    mut v_name_1130_: *mut leanh::LeanObject,
    mut v_kind_1131_: u8,
    mut v___y_1132_: *mut leanh::LeanObject,
    mut v___y_1133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ =
        l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(
            v_name_1130_,
            v_kind_1131_,
            v___y_1132_,
            v___y_1133_,
        );
    return v___x_1135_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___boxed(
    mut v_00_u03b1_1136_: *mut leanh::LeanObject,
    mut v_name_1137_: *mut leanh::LeanObject,
    mut v_kind_1138_: *mut leanh::LeanObject,
    mut v___y_1139_: *mut leanh::LeanObject,
    mut v___y_1140_: *mut leanh::LeanObject,
    mut v___y_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_1142_: u8 = 0;
    let mut v_res_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1142_ = (leanh::lean_unbox(v_kind_1138_) as u8);
    v_res_1143_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(
        v_00_u03b1_1136_,
        v_name_1137_,
        v_kind_boxed_1142_,
        v___y_1139_,
        v___y_1140_,
    );
    leanh::lean_dec(v___y_1140_);
    leanh::lean_dec_ref(v___y_1139_);
    return v_res_1143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(
    mut v_a_1144_: *mut leanh::LeanObject,
    mut v_as_1145_: *mut leanh::LeanObject,
    mut v_i_1146_: usize,
    mut v_stop_1147_: usize,
) -> u8 {
    let mut v___x_1148_: u8 = 0;
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: usize = 0;
    let mut v___x_1152_: usize = 0;
    let mut v___x_1154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1148_ = lean_usize_dec_eq(v_i_1146_, v_stop_1147_);
                if v___x_1148_ == 0 {
                    v___x_1149_ = lean_array_uget_borrowed(v_as_1145_, v_i_1146_);
                    v___x_1150_ = lean_name_eq(v_a_1144_, v___x_1149_);
                    if v___x_1150_ == 0 {
                        v___x_1151_ = 1usize;
                        v___x_1152_ = lean_usize_add(v_i_1146_, v___x_1151_);
                        v_i_1146_ = v___x_1152_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1150_;
                    }
                } else {
                    v___x_1154_ = 0;
                    return v___x_1154_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0___boxed(
    mut v_a_1155_: *mut leanh::LeanObject,
    mut v_as_1156_: *mut leanh::LeanObject,
    mut v_i_1157_: *mut leanh::LeanObject,
    mut v_stop_1158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1159_: usize = 0;
    let mut v_stop_boxed_1160_: usize = 0;
    let mut v_res_1161_: u8 = 0;
    let mut v_r_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1159_ = leanh::lean_unbox_usize(v_i_1157_);
    leanh::lean_dec(v_i_1157_);
    v_stop_boxed_1160_ = leanh::lean_unbox_usize(v_stop_1158_);
    leanh::lean_dec(v_stop_1158_);
    v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_1155_, v_as_1156_, v_i_boxed_1159_, v_stop_boxed_1160_);
    leanh::lean_dec_ref(v_as_1156_);
    leanh::lean_dec(v_a_1155_);
    v_r_1162_ = leanh::lean_box((v_res_1161_) as usize);
    return v_r_1162_;
}
pub unsafe fn l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(
    mut v_as_1163_: *mut leanh::LeanObject,
    mut v_a_1164_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    v___x_1165_ = leanh::lean_unsigned_to_nat(0);
    v___x_1166_ = lean_array_get_size(v_as_1163_);
    v___x_1167_ = lean_nat_dec_lt(v___x_1165_, v___x_1166_);
    if v___x_1167_ == 0 {
        return v___x_1167_;
    } else {
        if v___x_1167_ == 0 {
            return v___x_1167_;
        } else {
            let mut v___x_1168_: usize = 0;
            let mut v___x_1169_: usize = 0;
            let mut v___x_1170_: u8 = 0;
            v___x_1168_ = 0usize;
            v___x_1169_ = lean_usize_of_nat(v___x_1166_);
            v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_1164_, v_as_1163_, v___x_1168_, v___x_1169_);
            return v___x_1170_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0___boxed(
    mut v_as_1171_: *mut leanh::LeanObject,
    mut v_a_1172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1173_: u8 = 0;
    let mut v_r_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ =
        l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(v_as_1171_, v_a_1172_);
    leanh::lean_dec(v_a_1172_);
    leanh::lean_dec_ref(v_as_1171_);
    v_r_1174_ = leanh::lean_box((v_res_1173_) as usize);
    return v_r_1174_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(
    mut v_as_1175_: *mut leanh::LeanObject,
    mut v_k_1176_: *mut leanh::LeanObject,
    mut v_x_1177_: *mut leanh::LeanObject,
    mut v_x_1178_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: u8 = 0;
    let mut v___x_1184_: u8 = 0;
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: u8 = 0;
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1179_ = lean_nat_add(v_x_1177_, v_x_1178_);
                v___x_1180_ = leanh::lean_unsigned_to_nat(1);
                v_m_1181_ = lean_nat_shiftr(v___x_1179_, v___x_1180_);
                leanh::lean_dec(v___x_1179_);
                v_a_1182_ = lean_array_fget_borrowed(v_as_1175_, v_m_1181_);
                v___x_1183_ = l_Lean_Name_quickLt(v_a_1182_, v_k_1176_);
                if v___x_1183_ == 0 {
                    leanh::lean_dec(v_x_1178_);
                    v___x_1184_ = l_Lean_Name_quickLt(v_k_1176_, v_a_1182_);
                    if v___x_1184_ == 0 {
                        leanh::lean_dec(v_m_1181_);
                        leanh::lean_dec(v_x_1177_);
                        v___x_1185_ = 1;
                        return v___x_1185_;
                    } else {
                        v___x_1186_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1187_ = lean_nat_dec_eq(v_m_1181_, v___x_1186_);
                        if v___x_1187_ == 0 {
                            v___x_1188_ = lean_nat_sub(v_m_1181_, v___x_1180_);
                            leanh::lean_dec(v_m_1181_);
                            v___x_1189_ = lean_nat_dec_lt(v___x_1188_, v_x_1177_);
                            if v___x_1189_ == 0 {
                                v_x_1178_ = v___x_1188_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1188_);
                                leanh::lean_dec(v_x_1177_);
                                return v___x_1183_;
                            }
                        } else {
                            leanh::lean_dec(v_m_1181_);
                            leanh::lean_dec(v_x_1177_);
                            return v___x_1183_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_x_1177_);
                    v___x_1191_ = lean_nat_add(v_m_1181_, v___x_1180_);
                    leanh::lean_dec(v_m_1181_);
                    v___x_1192_ = lean_nat_dec_le(v___x_1191_, v_x_1178_);
                    if v___x_1192_ == 0 {
                        leanh::lean_dec(v___x_1191_);
                        leanh::lean_dec(v_x_1178_);
                        return v___x_1192_;
                    } else {
                        v_x_1177_ = v___x_1191_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg___boxed(
    mut v_as_1194_: *mut leanh::LeanObject,
    mut v_k_1195_: *mut leanh::LeanObject,
    mut v_x_1196_: *mut leanh::LeanObject,
    mut v_x_1197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1198_: u8 = 0;
    let mut v_r_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(
        v_as_1194_, v_k_1195_, v_x_1196_, v_x_1197_,
    );
    leanh::lean_dec(v_k_1195_);
    leanh::lean_dec_ref(v_as_1194_);
    v_r_1199_ = leanh::lean_box((v_res_1198_) as usize);
    return v_r_1199_;
}
pub unsafe fn _init_l_Lake_OrderedTagAttribute_hasTag___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1200_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_1200_;
}
pub unsafe fn l_Lake_OrderedTagAttribute_hasTag(
    mut v_attr_1201_: *mut leanh::LeanObject,
    mut v_env_1202_: *mut leanh::LeanObject,
    mut v_decl_1203_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_hasTag___closed__0),
        core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_hasTag___closed__0_once),
        _init_l_Lake_OrderedTagAttribute_hasTag___closed__0,
    );
    v___x_1205_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1202_, v_decl_1203_);
    if leanh::lean_obj_tag(v___x_1205_) == 0 {
        let mut v_ext_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toEnvExtension_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: u8 = 0;
        v_ext_1206_ = leanh::lean_ctor_get(v_attr_1201_, 1);
        v_toEnvExtension_1207_ = leanh::lean_ctor_get(v_ext_1206_, 0);
        v_asyncMode_1208_ = leanh::lean_ctor_get(v_toEnvExtension_1207_, 2);
        v___x_1209_ = leanh::lean_box(0);
        v___x_1210_ = l_Lean_PersistentEnvExtension_getState___redArg(
            v___x_1204_,
            v_ext_1206_,
            v_env_1202_,
            v_asyncMode_1208_,
            v___x_1209_,
        );
        v___x_1211_ = l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(
            v___x_1210_,
            v_decl_1203_,
        );
        leanh::lean_dec(v___x_1210_);
        return v___x_1211_;
    } else {
        let mut v_val_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ext_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1214_: u8 = 0;
        let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1218_: u8 = 0;
        v_val_1212_ = leanh::lean_ctor_get(v___x_1205_, 0);
        leanh::lean_inc(v_val_1212_);
        leanh::lean_dec_ref_known(v___x_1205_, 1);
        v_ext_1213_ = leanh::lean_ctor_get(v_attr_1201_, 1);
        v___x_1214_ = 0;
        v___x_1215_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
            v___x_1204_,
            v_ext_1213_,
            v_env_1202_,
            v_val_1212_,
            v___x_1214_,
        );
        leanh::lean_dec(v_val_1212_);
        leanh::lean_dec_ref(v_env_1202_);
        v___x_1216_ = leanh::lean_unsigned_to_nat(0);
        v___x_1217_ = lean_array_get_size(v___x_1215_);
        v___x_1218_ = lean_nat_dec_lt(v___x_1216_, v___x_1217_);
        if v___x_1218_ == 0 {
            leanh::lean_dec_ref(v___x_1215_);
            return v___x_1218_;
        } else {
            let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1221_: u8 = 0;
            v___x_1219_ = leanh::lean_unsigned_to_nat(1);
            v___x_1220_ = lean_nat_sub(v___x_1217_, v___x_1219_);
            v___x_1221_ = lean_nat_dec_le(v___x_1216_, v___x_1220_);
            if v___x_1221_ == 0 {
                leanh::lean_dec(v___x_1220_);
                leanh::lean_dec_ref(v___x_1215_);
                return v___x_1221_;
            } else {
                let mut v___x_1222_: u8 = 0;
                v___x_1222_ =
                    l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(
                        v___x_1215_,
                        v_decl_1203_,
                        v___x_1216_,
                        v___x_1220_,
                    );
                leanh::lean_dec_ref(v___x_1215_);
                return v___x_1222_;
            }
        }
    }
}
pub unsafe fn l_Lake_OrderedTagAttribute_hasTag___boxed(
    mut v_attr_1223_: *mut leanh::LeanObject,
    mut v_env_1224_: *mut leanh::LeanObject,
    mut v_decl_1225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1226_: u8 = 0;
    let mut v_r_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1226_ = l_Lake_OrderedTagAttribute_hasTag(v_attr_1223_, v_env_1224_, v_decl_1225_);
    leanh::lean_dec(v_decl_1225_);
    leanh::lean_dec_ref(v_attr_1223_);
    v_r_1227_ = leanh::lean_box((v_res_1226_) as usize);
    return v_r_1227_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(
    mut v_as_1228_: *mut leanh::LeanObject,
    mut v_k_1229_: *mut leanh::LeanObject,
    mut v_x_1230_: *mut leanh::LeanObject,
    mut v_x_1231_: *mut leanh::LeanObject,
    mut v_x_1232_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1233_: u8 = 0;
    v___x_1233_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(
        v_as_1228_, v_k_1229_, v_x_1230_, v_x_1231_,
    );
    return v___x_1233_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___boxed(
    mut v_as_1234_: *mut leanh::LeanObject,
    mut v_k_1235_: *mut leanh::LeanObject,
    mut v_x_1236_: *mut leanh::LeanObject,
    mut v_x_1237_: *mut leanh::LeanObject,
    mut v_x_1238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1239_: u8 = 0;
    let mut v_r_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(
        v_as_1234_, v_k_1235_, v_x_1236_, v_x_1237_, v_x_1238_,
    );
    leanh::lean_dec(v_k_1235_);
    leanh::lean_dec_ref(v_as_1234_);
    v_r_1240_ = leanh::lean_box((v_res_1239_) as usize);
    return v_r_1240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(
    mut v_as_1241_: *mut leanh::LeanObject,
    mut v_i_1242_: usize,
    mut v_stop_1243_: usize,
    mut v_b_1244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: usize = 0;
    let mut v___x_1249_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1245_ = lean_usize_dec_eq(v_i_1242_, v_stop_1243_);
                if v___x_1245_ == 0 {
                    v___x_1246_ = lean_array_uget_borrowed(v_as_1241_, v_i_1242_);
                    v___x_1247_ = l_Array_append___redArg(v_b_1244_, v___x_1246_);
                    v___x_1248_ = 1usize;
                    v___x_1249_ = lean_usize_add(v_i_1242_, v___x_1248_);
                    v_i_1242_ = v___x_1249_;
                    v_b_1244_ = v___x_1247_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1244_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0___boxed(
    mut v_as_1251_: *mut leanh::LeanObject,
    mut v_i_1252_: *mut leanh::LeanObject,
    mut v_stop_1253_: *mut leanh::LeanObject,
    mut v_b_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1255_: usize = 0;
    let mut v_stop_boxed_1256_: usize = 0;
    let mut v_res_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1255_ = leanh::lean_unbox_usize(v_i_1252_);
    leanh::lean_dec(v_i_1252_);
    v_stop_boxed_1256_ = leanh::lean_unbox_usize(v_stop_1253_);
    leanh::lean_dec(v_stop_1253_);
    v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_as_1251_, v_i_boxed_1255_, v_stop_boxed_1256_, v_b_1254_);
    leanh::lean_dec_ref(v_as_1251_);
    return v_res_1257_;
}
pub unsafe fn _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1258_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_hasTag___closed__0),
        core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_hasTag___closed__0_once),
        _init_l_Lake_OrderedTagAttribute_hasTag___closed__0,
    );
    v___x_1259_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1258_);
    return v___x_1259_;
}
pub unsafe fn l_Lake_OrderedTagAttribute_getAllEntries(
    mut v_attr_1260_: *mut leanh::LeanObject,
    mut v_env_1261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ext_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: usize = 0;
    let mut v___x_1279_: usize = 0;
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: usize = 0;
    let mut v___x_1282_: usize = 0;
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ext_1262_ = leanh::lean_ctor_get(v_attr_1260_, 1);
                v_toEnvExtension_1263_ = leanh::lean_ctor_get(v_ext_1262_, 0);
                v_asyncMode_1264_ = leanh::lean_ctor_get(v_toEnvExtension_1263_, 2);
                v___x_1265_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_getAllEntries___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lake_OrderedTagAttribute_getAllEntries___closed__0_once
                    ),
                    _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0,
                );
                v___x_1266_ = leanh::lean_box(0);
                v_s_1267_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1265_,
                        v_toEnvExtension_1263_,
                        v_env_1261_,
                        v_asyncMode_1264_,
                        v___x_1266_,
                    );
                v_importedEntries_1272_ = leanh::lean_ctor_get(v_s_1267_, 0);
                leanh::lean_inc_ref(v_importedEntries_1272_);
                v___x_1273_ = leanh::lean_unsigned_to_nat(0);
                v___x_1274_ = l_Lake_registerOrderedTagAttribute___closed__4;
                v___x_1275_ = lean_array_get_size(v_importedEntries_1272_);
                v___x_1276_ = lean_nat_dec_lt(v___x_1273_, v___x_1275_);
                if v___x_1276_ == 0 {
                    leanh::lean_dec_ref(v_importedEntries_1272_);
                    v___y_1269_ = v___x_1274_;
                    state = 1;
                    continue;
                } else {
                    v___x_1277_ = lean_nat_dec_le(v___x_1275_, v___x_1275_);
                    if v___x_1277_ == 0 {
                        if v___x_1276_ == 0 {
                            leanh::lean_dec_ref(v_importedEntries_1272_);
                            v___y_1269_ = v___x_1274_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1278_ = 0usize;
                            v___x_1279_ = lean_usize_of_nat(v___x_1275_);
                            v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_importedEntries_1272_, v___x_1278_, v___x_1279_, v___x_1274_);
                            leanh::lean_dec_ref(v_importedEntries_1272_);
                            v___y_1269_ = v___x_1280_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1281_ = 0usize;
                        v___x_1282_ = lean_usize_of_nat(v___x_1275_);
                        v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_importedEntries_1272_, v___x_1281_, v___x_1282_, v___x_1274_);
                        leanh::lean_dec_ref(v_importedEntries_1272_);
                        v___y_1269_ = v___x_1283_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_state_1270_ = leanh::lean_ctor_get(v_s_1267_, 1);
                leanh::lean_inc(v_state_1270_);
                leanh::lean_dec(v_s_1267_);
                v___x_1271_ = l_Array_append___redArg(v___y_1269_, v_state_1270_);
                leanh::lean_dec(v_state_1270_);
                return v___x_1271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_OrderedTagAttribute_getAllEntries___boxed(
    mut v_attr_1284_: *mut leanh::LeanObject,
    mut v_env_1285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1286_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_1284_, v_env_1285_);
    leanh::lean_dec_ref(v_attr_1284_);
    return v_res_1286_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_OrderedTagAttribute(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_instInhabitedOrderedTagAttribute_default =
        _init_l_Lake_instInhabitedOrderedTagAttribute_default();
    leanh::lean_mark_persistent(l_Lake_instInhabitedOrderedTagAttribute_default);
    l_Lake_instInhabitedOrderedTagAttribute = _init_l_Lake_instInhabitedOrderedTagAttribute();
    leanh::lean_mark_persistent(l_Lake_instInhabitedOrderedTagAttribute);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_OrderedTagAttribute(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lake_registerOrderedTagAttribute___auto__1 =
        _init_l_Lake_registerOrderedTagAttribute___auto__1();
    leanh::lean_mark_persistent(l_Lake_registerOrderedTagAttribute___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_OrderedTagAttribute(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OrderedTagAttribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_OrderedTagAttribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_OrderedTagAttribute(builtin);
}
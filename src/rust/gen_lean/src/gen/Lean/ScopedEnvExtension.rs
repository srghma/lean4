// Lean compiler output
// Module: Lean.ScopedEnvExtension
// Imports: Lean.Attributes
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_st_mk_ref, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop, l_Array_reverse___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_mkAtom, l_List_lengthTR___redArg, l_id___boxed, l_panic___redArg,
};
use crate::r#gen::Init::System::IO::l_instInhabitedEIO___aux__1___boxed;
use crate::r#gen::Init::System::IOError::l_instInhabitedError;
use crate::r#gen::Init::System::ST::l_ST_Prim_Ref_get___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_PersistentEnvExtension_modifyState___redArg, l_Lean_instInhabitedEnvExtension_default,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value:
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value:
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value:
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3_value:
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_1:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_2:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5_value:
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6_value:
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_1:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_2:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8_value:
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10_value:
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_1:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_2:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10_value)
            as *mut crate::leanh::LeanObject,
        14997215300048349804 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_1:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_2:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value:
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15_value)
            as *mut crate::leanh::LeanObject,
        7677164612348466033 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0_value:
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
    m_fun: l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1_value:
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
    m_fun: l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2_value:
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
    m_fun: l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value:
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
static mut l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0_value:
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
    m_fun: l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1_value:
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
    m_fun: l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2_value:
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
    m_fun: l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3_value:
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
    m_fun: l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_scopedEnvExtensionsRef: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value:
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
    m_fun: l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1_value:
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
    m_fun: l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0_value:
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
    m_fun: l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_popScope___redArg___closed__0_value:
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
    m_fun: l_Lean_ScopedEnvExtension_popScope___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ScopedEnvExtension_popScope___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_getState___redArg___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        76, 101, 97, 110, 46, 83, 99, 111, 112, 101, 100, 69, 110, 118, 69, 120, 116, 101, 110,
        115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_getState___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_getState___redArg___closed__1_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 83, 99, 111, 112, 101, 100, 69, 110, 118, 69, 120, 116, 101, 110,
        115, 105, 111, 110, 46, 103, 101, 116, 83, 116, 97, 116, 101, 0,
    ],
};
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_getState___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ScopedEnvExtension_getState___redArg___closed__2_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_getState___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_pushScope___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_pushScope___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0_value:
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
    m_fun: l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1_value:
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
    m_fun: l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(
    mut v_x_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2602_) == 0 {
        let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2603_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2603_;
    } else {
        let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2604_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2604_;
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg___boxed(
    mut v_x_2605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2606_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(v_x_2605_);
    crate::leanh::lean_dec_ref(v_x_2605_);
    return v_res_2606_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorIdx(
    mut v_00_u03b1_2607_: *mut crate::leanh::LeanObject,
    mut v_x_2608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(v_x_2608_);
    return v___x_2609_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorIdx___boxed(
    mut v_00_u03b1_2610_: *mut crate::leanh::LeanObject,
    mut v_x_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2612_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx(v_00_u03b1_2610_, v_x_2611_);
    crate::leanh::lean_dec_ref(v_x_2611_);
    return v_res_2612_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(
    mut v_t_2613_: *mut crate::leanh::LeanObject,
    mut v_k_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2613_) == 0 {
        let mut v_a_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2615_ = crate::leanh::lean_ctor_get(v_t_2613_, 0);
        crate::leanh::lean_inc(v_a_2615_);
        crate::leanh::lean_dec_ref_known(v_t_2613_, 1);
        v___x_2616_ = crate::leanh::lean_apply_1(v_k_2614_, v_a_2615_);
        return v___x_2616_;
    } else {
        let mut v_a_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2617_ = crate::leanh::lean_ctor_get(v_t_2613_, 0);
        crate::leanh::lean_inc(v_a_2617_);
        v_a_2618_ = crate::leanh::lean_ctor_get(v_t_2613_, 1);
        crate::leanh::lean_inc(v_a_2618_);
        crate::leanh::lean_dec_ref_known(v_t_2613_, 2);
        v___x_2619_ = crate::leanh::lean_apply_2(v_k_2614_, v_a_2617_, v_a_2618_);
        return v___x_2619_;
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorElim(
    mut v_00_u03b1_2620_: *mut crate::leanh::LeanObject,
    mut v_motive_2621_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2622_: *mut crate::leanh::LeanObject,
    mut v_t_2623_: *mut crate::leanh::LeanObject,
    mut v_h_2624_: *mut crate::leanh::LeanObject,
    mut v_k_2625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2626_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2623_, v_k_2625_);
    return v___x_2626_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorElim___boxed(
    mut v_00_u03b1_2627_: *mut crate::leanh::LeanObject,
    mut v_motive_2628_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2629_: *mut crate::leanh::LeanObject,
    mut v_t_2630_: *mut crate::leanh::LeanObject,
    mut v_h_2631_: *mut crate::leanh::LeanObject,
    mut v_k_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2633_ = l_Lean_ScopedEnvExtension_Entry_ctorElim(
        v_00_u03b1_2627_,
        v_motive_2628_,
        v_ctorIdx_2629_,
        v_t_2630_,
        v_h_2631_,
        v_k_2632_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2629_);
    return v_res_2633_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_global_elim___redArg(
    mut v_t_2634_: *mut crate::leanh::LeanObject,
    mut v_global_2635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2634_, v_global_2635_);
    return v___x_2636_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_global_elim(
    mut v_00_u03b1_2637_: *mut crate::leanh::LeanObject,
    mut v_motive_2638_: *mut crate::leanh::LeanObject,
    mut v_t_2639_: *mut crate::leanh::LeanObject,
    mut v_h_2640_: *mut crate::leanh::LeanObject,
    mut v_global_2641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2639_, v_global_2641_);
    return v___x_2642_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_scoped_elim___redArg(
    mut v_t_2643_: *mut crate::leanh::LeanObject,
    mut v_scoped_2644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2643_, v_scoped_2644_);
    return v___x_2645_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_scoped_elim(
    mut v_00_u03b1_2646_: *mut crate::leanh::LeanObject,
    mut v_motive_2647_: *mut crate::leanh::LeanObject,
    mut v_t_2648_: *mut crate::leanh::LeanObject,
    mut v_h_2649_: *mut crate::leanh::LeanObject,
    mut v_scoped_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2651_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2648_, v_scoped_2650_);
    return v___x_2651_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2652_ = crate::leanh::lean_box(0);
    v___x_2653_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2654_ = lean_mk_array(v___x_2653_, v___x_2652_);
    return v___x_2654_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0,
    );
    v___x_2656_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2657_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2657_, 0, v___x_2656_);
    crate::leanh::lean_ctor_set(v___x_2657_, 1, v___x_2655_);
    return v___x_2657_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2658_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2658_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2659_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2,
    );
    v___x_2660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2660_, 0, v___x_2659_);
    return v___x_2660_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2661_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3,
    );
    v___x_2662_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1,
    );
    v___x_2663_ = 1;
    v___x_2664_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2664_, 0, v___x_2662_);
    crate::leanh::lean_ctor_set(v___x_2664_, 1, v___x_2661_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2664_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_2663_,
    );
    return v___x_2664_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(
    mut v_00_u03b2_2665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2666_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4,
    );
    return v___x_2666_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ =
        l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(crate::leanh::lean_box(0));
    return v___x_2667_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(
    mut v_a_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2669_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0,
    );
    return v___x_2669_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2670_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4,
    );
    v___x_2671_ = crate::leanh::lean_box(0);
    v___x_2672_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2672_, 0, v___x_2671_);
    crate::leanh::lean_ctor_set(v___x_2672_, 1, v___x_2670_);
    crate::leanh::lean_ctor_set(v___x_2672_, 2, v___x_2671_);
    return v___x_2672_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(
    mut v_00_u03b1_2673_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2674_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2676_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0,
    );
    return v___x_2676_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2677_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2677_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedStateStack(
    mut v_a_2678_: *mut crate::leanh::LeanObject,
    mut v_a_2679_: *mut crate::leanh::LeanObject,
    mut v_a_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2681_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once),
        _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0,
    );
    return v___x_2681_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2708_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10;
    v___x_2709_ = l_Lean_mkAtom(v___x_2708_);
    return v___x_2709_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12,
    );
    v___x_2711_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2712_ = lean_array_push(v___x_2711_, v___x_2710_);
    return v___x_2712_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17;
    v___x_2722_ = l_Lean_mkAtom(v___x_2721_);
    return v___x_2722_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18,
    );
    v___x_2724_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2725_ = lean_array_push(v___x_2724_, v___x_2723_);
    return v___x_2725_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2726_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19,
    );
    v___x_2727_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16;
    v___x_2728_ = crate::leanh::lean_box(2);
    v___x_2729_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2729_, 0, v___x_2728_);
    crate::leanh::lean_ctor_set(v___x_2729_, 1, v___x_2727_);
    crate::leanh::lean_ctor_set(v___x_2729_, 2, v___x_2726_);
    return v___x_2729_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20,
    );
    v___x_2731_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13,
    );
    v___x_2732_ = lean_array_push(v___x_2731_, v___x_2730_);
    return v___x_2732_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21,
    );
    v___x_2734_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11;
    v___x_2735_ = crate::leanh::lean_box(2);
    v___x_2736_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2736_, 0, v___x_2735_);
    crate::leanh::lean_ctor_set(v___x_2736_, 1, v___x_2734_);
    crate::leanh::lean_ctor_set(v___x_2736_, 2, v___x_2733_);
    return v___x_2736_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2737_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22,
    );
    v___x_2738_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2739_ = lean_array_push(v___x_2738_, v___x_2737_);
    return v___x_2739_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2740_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23,
    );
    v___x_2741_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9;
    v___x_2742_ = crate::leanh::lean_box(2);
    v___x_2743_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2743_, 0, v___x_2742_);
    crate::leanh::lean_ctor_set(v___x_2743_, 1, v___x_2741_);
    crate::leanh::lean_ctor_set(v___x_2743_, 2, v___x_2740_);
    return v___x_2743_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2744_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24,
    );
    v___x_2745_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2746_ = lean_array_push(v___x_2745_, v___x_2744_);
    return v___x_2746_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2747_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25,
    );
    v___x_2748_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7;
    v___x_2749_ = crate::leanh::lean_box(2);
    v___x_2750_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2750_, 0, v___x_2749_);
    crate::leanh::lean_ctor_set(v___x_2750_, 1, v___x_2748_);
    crate::leanh::lean_ctor_set(v___x_2750_, 2, v___x_2747_);
    return v___x_2750_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2751_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26,
    );
    v___x_2752_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2753_ = lean_array_push(v___x_2752_, v___x_2751_);
    return v___x_2753_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27,
    );
    v___x_2755_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4;
    v___x_2756_ = crate::leanh::lean_box(2);
    v___x_2757_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2757_, 0, v___x_2756_);
    crate::leanh::lean_ctor_set(v___x_2757_, 1, v___x_2755_);
    crate::leanh::lean_ctor_set(v___x_2757_, 2, v___x_2754_);
    return v___x_2757_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2758_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28,
    );
    return v___x_2758_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(
    mut v_x_2762_: *mut crate::leanh::LeanObject,
    mut v___y_2763_: *mut crate::leanh::LeanObject,
    mut v___y_2764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2766_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1;
    v___x_2767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2766_);
    return v___x_2767_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(
    mut v_x_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
    mut v___y_2770_: *mut crate::leanh::LeanObject,
    mut v___y_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(
        v_x_2768_,
        v___y_2769_,
        v___y_2770_,
    );
    crate::leanh::lean_dec_ref(v___y_2770_);
    crate::leanh::lean_dec(v___y_2769_);
    crate::leanh::lean_dec(v_x_2768_);
    return v_res_2772_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(
    mut v_inst_2773_: *mut crate::leanh::LeanObject,
    mut v_x_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_2773_);
    return v_inst_2773_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(
    mut v_inst_2775_: *mut crate::leanh::LeanObject,
    mut v_x_2776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2777_ =
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_inst_2775_, v_x_2776_);
    crate::leanh::lean_dec(v_x_2776_);
    crate::leanh::lean_dec(v_inst_2775_);
    return v_res_2777_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(
    mut v_s_2778_: *mut crate::leanh::LeanObject,
    mut v_x_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_s_2778_);
    return v_s_2778_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(
    mut v_s_2780_: *mut crate::leanh::LeanObject,
    mut v_x_2781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2782_ =
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_s_2780_, v_x_2781_);
    crate::leanh::lean_dec(v_x_2781_);
    crate::leanh::lean_dec(v_s_2780_);
    return v_res_2782_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(
    mut v_x_2783_: *mut crate::leanh::LeanObject,
    mut v_a_2784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2785_, 0, v_a_2784_);
    crate::leanh::lean_inc_ref_n(v___x_2785_, 2);
    v___x_2786_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2786_, 0, v___x_2785_);
    crate::leanh::lean_ctor_set(v___x_2786_, 1, v___x_2785_);
    crate::leanh::lean_ctor_set(v___x_2786_, 2, v___x_2785_);
    return v___x_2786_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(
    mut v_x_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2789_ =
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_2787_, v_a_2788_);
    crate::leanh::lean_dec_ref(v_x_2787_);
    return v_res_2789_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2793_ = l_instInhabitedError;
    v___x_2794_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2794_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2794_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2794_, 2, v___x_2793_);
    return v___x_2794_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(
    mut v_inst_2796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2797_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0;
    v___f_2798_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2798_, 0, v_inst_2796_);
    v___f_2799_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1;
    v___f_2800_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2;
    v___x_2801_ = crate::leanh::lean_box(0);
    v___x_2802_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3,
    );
    v___x_2803_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4;
    v___x_2804_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2804_, 0, v___x_2801_);
    crate::leanh::lean_ctor_set(v___x_2804_, 1, v___x_2802_);
    crate::leanh::lean_ctor_set(v___x_2804_, 2, v___f_2797_);
    crate::leanh::lean_ctor_set(v___x_2804_, 3, v___f_2798_);
    crate::leanh::lean_ctor_set(v___x_2804_, 4, v___f_2799_);
    crate::leanh::lean_ctor_set(v___x_2804_, 5, v___x_2803_);
    crate::leanh::lean_ctor_set(v___x_2804_, 6, v___f_2800_);
    return v___x_2804_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr(
    mut v_00_u03b1_2805_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2806_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2807_: *mut crate::leanh::LeanObject,
    mut v_inst_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2809_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_2808_);
    return v___x_2809_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_mkInitial___redArg(
    mut v_descr_2810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mkInitial_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2817_: u8 = 0;
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: u8 = 0;
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_a_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mkInitial_2812_ = crate::leanh::lean_ctor_get(v_descr_2810_, 1);
                crate::leanh::lean_inc_ref(v_mkInitial_2812_);
                crate::leanh::lean_dec_ref(v_descr_2810_);
                v___x_2813_ =
                    crate::leanh::lean_apply_1(v_mkInitial_2812_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_2813_) == 0 {
                    v_a_2814_ = crate::leanh::lean_ctor_get(v___x_2813_, 0);
                    v_isSharedCheck_2828_ = (!crate::leanh::lean_is_exclusive(v___x_2813_)) as u8;
                    if v_isSharedCheck_2828_ == 0 {
                        v___x_2816_ = v___x_2813_;
                        v_isShared_2817_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2814_);
                        crate::leanh::lean_dec(v___x_2813_);
                        v___x_2816_ = crate::leanh::lean_box(0);
                        v_isShared_2817_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2829_ = crate::leanh::lean_ctor_get(v___x_2813_, 0);
                    v_isSharedCheck_2836_ = (!crate::leanh::lean_is_exclusive(v___x_2813_)) as u8;
                    if v_isSharedCheck_2836_ == 0 {
                        v___x_2831_ = v___x_2813_;
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2829_);
                        crate::leanh::lean_dec(v___x_2813_);
                        v___x_2831_ = crate::leanh::lean_box(0);
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2818_ = l_Lean_NameSet_empty;
                v___x_2819_ = 1;
                v___x_2820_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2820_, 0, v_a_2814_);
                crate::leanh::lean_ctor_set(v___x_2820_, 1, v___x_2818_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2819_,
                );
                v___x_2821_ = crate::leanh::lean_box(0);
                v___x_2822_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2822_, 0, v___x_2820_);
                crate::leanh::lean_ctor_set(v___x_2822_, 1, v___x_2821_);
                v___x_2823_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once), _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
                v___x_2824_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2824_, 0, v___x_2822_);
                crate::leanh::lean_ctor_set(v___x_2824_, 1, v___x_2823_);
                crate::leanh::lean_ctor_set(v___x_2824_, 2, v___x_2821_);
                if v_isShared_2817_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2816_, 0, v___x_2824_);
                    v___x_2826_ = v___x_2816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2827_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
                    v___x_2826_ = v_reuseFailAlloc_2827_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2826_;
            }
            3 => {
                if v_isShared_2832_ == 0 {
                    v___x_2834_ = v___x_2831_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(
    mut v_descr_2837_: *mut crate::leanh::LeanObject,
    mut v_a_2838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2839_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_2837_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_mkInitial(
    mut v_00_u03b1_2840_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2841_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2842_: *mut crate::leanh::LeanObject,
    mut v_descr_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2845_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_2843_);
    return v___x_2845_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_mkInitial___boxed(
    mut v_00_u03b1_2846_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2847_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2848_: *mut crate::leanh::LeanObject,
    mut v_descr_2849_: *mut crate::leanh::LeanObject,
    mut v_a_2850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2851_ = l_Lean_ScopedEnvExtension_mkInitial(
        v_00_u03b1_2846_,
        v_00_u03b2_2847_,
        v_00_u03c3_2848_,
        v_descr_2849_,
    );
    return v_res_2851_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(
    mut v_a_2852_: *mut crate::leanh::LeanObject,
    mut v_x_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: u8 = 0;
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2853_) == 0 {
                    v___x_2854_ = crate::leanh::lean_box(0);
                    return v___x_2854_;
                } else {
                    v_key_2855_ = crate::leanh::lean_ctor_get(v_x_2853_, 0);
                    v_value_2856_ = crate::leanh::lean_ctor_get(v_x_2853_, 1);
                    v_tail_2857_ = crate::leanh::lean_ctor_get(v_x_2853_, 2);
                    v___x_2858_ = lean_name_eq(v_key_2855_, v_a_2852_);
                    if v___x_2858_ == 0 {
                        v_x_2853_ = v_tail_2857_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2856_);
                        v___x_2860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2860_, 0, v_value_2856_);
                        return v___x_2860_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_2861_: *mut crate::leanh::LeanObject,
    mut v_x_2862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_2861_, v_x_2862_);
    crate::leanh::lean_dec(v_x_2862_);
    crate::leanh::lean_dec(v_a_2861_);
    return v_res_2863_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: u64 = 0;
    v___x_2864_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_2865_ = lean_uint64_of_nat(v___x_2864_);
    return v___x_2865_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(
    mut v_m_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2871_: u64 = 0;
    let mut v___x_2872_: u64 = 0;
    let mut v___x_2873_: u64 = 0;
    let mut v_fold_2874_: u64 = 0;
    let mut v___x_2875_: u64 = 0;
    let mut v___x_2876_: u64 = 0;
    let mut v___x_2877_: u64 = 0;
    let mut v___x_2878_: usize = 0;
    let mut v___x_2879_: usize = 0;
    let mut v___x_2880_: usize = 0;
    let mut v___x_2881_: usize = 0;
    let mut v___x_2882_: usize = 0;
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: u64 = 0;
    let mut v_hash_2886_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2868_ = crate::leanh::lean_ctor_get(v_m_2866_, 1);
                v___x_2869_ = lean_array_get_size(v_buckets_2868_);
                if crate::leanh::lean_obj_tag(v_a_2867_) == 0 {
                    v___x_2885_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_2871_ = v___x_2885_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2886_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_2867_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2871_ = v_hash_2886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2872_ = 32u64;
                v___x_2873_ = lean_uint64_shift_right(v___y_2871_, v___x_2872_);
                v_fold_2874_ = lean_uint64_xor(v___y_2871_, v___x_2873_);
                v___x_2875_ = 16u64;
                v___x_2876_ = lean_uint64_shift_right(v_fold_2874_, v___x_2875_);
                v___x_2877_ = lean_uint64_xor(v_fold_2874_, v___x_2876_);
                v___x_2878_ = lean_uint64_to_usize(v___x_2877_);
                v___x_2879_ = lean_usize_of_nat(v___x_2869_);
                v___x_2880_ = 1usize;
                v___x_2881_ = lean_usize_sub(v___x_2879_, v___x_2880_);
                v___x_2882_ = lean_usize_land(v___x_2878_, v___x_2881_);
                v___x_2883_ = lean_array_uget_borrowed(v_buckets_2868_, v___x_2882_);
                v___x_2884_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_2867_, v___x_2883_);
                return v___x_2884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(
    mut v_m_2887_: *mut crate::leanh::LeanObject,
    mut v_a_2888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_2887_, v_a_2888_);
    crate::leanh::lean_dec(v_a_2888_);
    crate::leanh::lean_dec_ref(v_m_2887_);
    return v_res_2889_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_2890_: *mut crate::leanh::LeanObject,
    mut v_vals_2891_: *mut crate::leanh::LeanObject,
    mut v_i_2892_: *mut crate::leanh::LeanObject,
    mut v_k_2893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2894_ = lean_array_get_size(v_keys_2890_);
                v___x_2895_ = lean_nat_dec_lt(v_i_2892_, v___x_2894_);
                if v___x_2895_ == 0 {
                    crate::leanh::lean_dec(v_i_2892_);
                    v___x_2896_ = crate::leanh::lean_box(0);
                    return v___x_2896_;
                } else {
                    v_k_x27_2897_ = lean_array_fget_borrowed(v_keys_2890_, v_i_2892_);
                    v___x_2898_ = lean_name_eq(v_k_2893_, v_k_x27_2897_);
                    if v___x_2898_ == 0 {
                        v___x_2899_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2900_ = lean_nat_add(v_i_2892_, v___x_2899_);
                        crate::leanh::lean_dec(v_i_2892_);
                        v_i_2892_ = v___x_2900_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2902_ = lean_array_fget_borrowed(v_vals_2891_, v_i_2892_);
                        crate::leanh::lean_dec(v_i_2892_);
                        crate::leanh::lean_inc(v___x_2902_);
                        v___x_2903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2903_, 0, v___x_2902_);
                        return v___x_2903_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_2904_: *mut crate::leanh::LeanObject,
    mut v_vals_2905_: *mut crate::leanh::LeanObject,
    mut v_i_2906_: *mut crate::leanh::LeanObject,
    mut v_k_2907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2908_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2904_, v_vals_2905_, v_i_2906_, v_k_2907_);
    crate::leanh::lean_dec(v_k_2907_);
    crate::leanh::lean_dec_ref(v_vals_2905_);
    crate::leanh::lean_dec_ref(v_keys_2904_);
    return v_res_2908_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_2909_: usize = 0;
    let mut v___x_2910_: usize = 0;
    let mut v___x_2911_: usize = 0;
    v___x_2909_ = 5usize;
    v___x_2910_ = 1usize;
    v___x_2911_ = lean_usize_shift_left(v___x_2910_, v___x_2909_);
    return v___x_2911_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_2912_: usize = 0;
    let mut v___x_2913_: usize = 0;
    let mut v___x_2914_: usize = 0;
    v___x_2912_ = 1usize;
    v___x_2913_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_2914_ = lean_usize_sub(v___x_2913_, v___x_2912_);
    return v___x_2914_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(
    mut v_x_2915_: *mut crate::leanh::LeanObject,
    mut v_x_2916_: usize,
    mut v_x_2917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: usize = 0;
    let mut v___x_2921_: usize = 0;
    let mut v___x_2922_: usize = 0;
    let mut v_j_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: u8 = 0;
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: usize = 0;
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2915_) == 0 {
                    v_es_2918_ = crate::leanh::lean_ctor_get(v_x_2915_, 0);
                    v___x_2919_ = crate::leanh::lean_box(2);
                    v___x_2920_ = 5usize;
                    v___x_2921_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2922_ = lean_usize_land(v_x_2916_, v___x_2921_);
                    v_j_2923_ = lean_usize_to_nat(v___x_2922_);
                    v___x_2924_ = lean_array_get_borrowed(v___x_2919_, v_es_2918_, v_j_2923_);
                    crate::leanh::lean_dec(v_j_2923_);
                    match crate::leanh::lean_obj_tag(v___x_2924_) {
                        0 => {
                            v_key_2925_ = crate::leanh::lean_ctor_get(v___x_2924_, 0);
                            v_val_2926_ = crate::leanh::lean_ctor_get(v___x_2924_, 1);
                            v___x_2927_ = lean_name_eq(v_x_2917_, v_key_2925_);
                            if v___x_2927_ == 0 {
                                v___x_2928_ = crate::leanh::lean_box(0);
                                return v___x_2928_;
                            } else {
                                crate::leanh::lean_inc(v_val_2926_);
                                v___x_2929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2929_, 0, v_val_2926_);
                                return v___x_2929_;
                            }
                        }
                        1 => {
                            v_node_2930_ = crate::leanh::lean_ctor_get(v___x_2924_, 0);
                            v___x_2931_ = lean_usize_shift_right(v_x_2916_, v___x_2920_);
                            v_x_2915_ = v_node_2930_;
                            v_x_2916_ = v___x_2931_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2933_ = crate::leanh::lean_box(0);
                            return v___x_2933_;
                        }
                    }
                } else {
                    v_ks_2934_ = crate::leanh::lean_ctor_get(v_x_2915_, 0);
                    v_vs_2935_ = crate::leanh::lean_ctor_get(v_x_2915_, 1);
                    v___x_2936_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2937_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2934_, v_vs_2935_, v___x_2936_, v_x_2917_);
                    return v___x_2937_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2938_: *mut crate::leanh::LeanObject,
    mut v_x_2939_: *mut crate::leanh::LeanObject,
    mut v_x_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1076__boxed_2941_: usize = 0;
    let mut v_res_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_2941_ = crate::leanh::lean_unbox_usize(v_x_2939_);
    crate::leanh::lean_dec(v_x_2939_);
    v_res_2942_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_2938_, v_x_1076__boxed_2941_, v_x_2940_);
    crate::leanh::lean_dec(v_x_2940_);
    crate::leanh::lean_dec_ref(v_x_2938_);
    return v_res_2942_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(
    mut v_x_2943_: *mut crate::leanh::LeanObject,
    mut v_x_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2946_: u64 = 0;
    let mut v___x_2947_: usize = 0;
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: u64 = 0;
    let mut v_hash_2950_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2944_) == 0 {
                    v___x_2949_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_2946_ = v___x_2949_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2950_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_2944_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2946_ = v_hash_2950_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2947_ = lean_uint64_to_usize(v___y_2946_);
                v___x_2948_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_2943_, v___x_2947_, v_x_2944_);
                return v___x_2948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_2951_: *mut crate::leanh::LeanObject,
    mut v_x_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_2951_, v_x_2952_);
    crate::leanh::lean_dec(v_x_2952_);
    crate::leanh::lean_dec_ref(v_x_2951_);
    return v_res_2953_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(
    mut v_x_2954_: *mut crate::leanh::LeanObject,
    mut v_x_2955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_2956_: u8 = 0;
    v_stage_u2081_2956_ = crate::leanh::lean_ctor_get_uint8(
        v_x_2954_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_2956_ == 0 {
        let mut v_map_u2081_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_2957_ = crate::leanh::lean_ctor_get(v_x_2954_, 0);
        v_map_u2082_2958_ = crate::leanh::lean_ctor_get(v_x_2954_, 1);
        v___x_2959_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_2958_, v_x_2955_);
        if crate::leanh::lean_obj_tag(v___x_2959_) == 0 {
            let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_2957_, v_x_2955_);
            return v___x_2960_;
        } else {
            return v___x_2959_;
        }
    } else {
        let mut v_map_u2081_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_2961_ = crate::leanh::lean_ctor_get(v_x_2954_, 0);
        v___x_2962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_2961_, v_x_2955_);
        return v___x_2962_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(
    mut v_x_2963_: *mut crate::leanh::LeanObject,
    mut v_x_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2965_ =
        l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(
            v_x_2963_, v_x_2964_,
        );
    crate::leanh::lean_dec(v_x_2964_);
    crate::leanh::lean_dec_ref(v_x_2963_);
    return v_res_2965_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(
    mut v_a_2966_: *mut crate::leanh::LeanObject,
    mut v_b_2967_: *mut crate::leanh::LeanObject,
    mut v_x_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2975_: u8 = 0;
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2968_) == 0 {
                    crate::leanh::lean_dec(v_b_2967_);
                    crate::leanh::lean_dec(v_a_2966_);
                    return v_x_2968_;
                } else {
                    v_key_2969_ = crate::leanh::lean_ctor_get(v_x_2968_, 0);
                    v_value_2970_ = crate::leanh::lean_ctor_get(v_x_2968_, 1);
                    v_tail_2971_ = crate::leanh::lean_ctor_get(v_x_2968_, 2);
                    v_isSharedCheck_2983_ = (!crate::leanh::lean_is_exclusive(v_x_2968_)) as u8;
                    if v_isSharedCheck_2983_ == 0 {
                        v___x_2973_ = v_x_2968_;
                        v_isShared_2974_ = v_isSharedCheck_2983_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2971_);
                        crate::leanh::lean_inc(v_value_2970_);
                        crate::leanh::lean_inc(v_key_2969_);
                        crate::leanh::lean_dec(v_x_2968_);
                        v___x_2973_ = crate::leanh::lean_box(0);
                        v_isShared_2974_ = v_isSharedCheck_2983_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2975_ = lean_name_eq(v_key_2969_, v_a_2966_);
                if v___x_2975_ == 0 {
                    v___x_2976_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_2966_, v_b_2967_, v_tail_2971_);
                    if v_isShared_2974_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2973_, 2, v___x_2976_);
                        v___x_2978_ = v___x_2973_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2979_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_key_2969_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_value_2970_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2979_, 2, v___x_2976_);
                        v___x_2978_ = v_reuseFailAlloc_2979_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_2970_);
                    crate::leanh::lean_dec(v_key_2969_);
                    if v_isShared_2974_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2973_, 1, v_b_2967_);
                        crate::leanh::lean_ctor_set(v___x_2973_, 0, v_a_2966_);
                        v___x_2981_ = v___x_2973_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2982_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2966_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_b_2967_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_tail_2971_);
                        v___x_2981_ = v_reuseFailAlloc_2982_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2978_;
            }
            3 => {
                return v___x_2981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(
    mut v_x_2984_: *mut crate::leanh::LeanObject,
    mut v_x_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2991_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2994_: u64 = 0;
    let mut v___x_2995_: u64 = 0;
    let mut v___x_2996_: u64 = 0;
    let mut v_fold_2997_: u64 = 0;
    let mut v___x_2998_: u64 = 0;
    let mut v___x_2999_: u64 = 0;
    let mut v___x_3000_: u64 = 0;
    let mut v___x_3001_: usize = 0;
    let mut v___x_3002_: usize = 0;
    let mut v___x_3003_: usize = 0;
    let mut v___x_3004_: usize = 0;
    let mut v___x_3005_: usize = 0;
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u64 = 0;
    let mut v_hash_3013_: u64 = 0;
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2985_) == 0 {
                    return v_x_2984_;
                } else {
                    v_key_2986_ = crate::leanh::lean_ctor_get(v_x_2985_, 0);
                    v_value_2987_ = crate::leanh::lean_ctor_get(v_x_2985_, 1);
                    v_tail_2988_ = crate::leanh::lean_ctor_get(v_x_2985_, 2);
                    v_isSharedCheck_3014_ = (!crate::leanh::lean_is_exclusive(v_x_2985_)) as u8;
                    if v_isSharedCheck_3014_ == 0 {
                        v___x_2990_ = v_x_2985_;
                        v_isShared_2991_ = v_isSharedCheck_3014_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2988_);
                        crate::leanh::lean_inc(v_value_2987_);
                        crate::leanh::lean_inc(v_key_2986_);
                        crate::leanh::lean_dec(v_x_2985_);
                        v___x_2990_ = crate::leanh::lean_box(0);
                        v_isShared_2991_ = v_isSharedCheck_3014_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2992_ = lean_array_get_size(v_x_2984_);
                if crate::leanh::lean_obj_tag(v_key_2986_) == 0 {
                    v___x_3012_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_2994_ = v___x_3012_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3013_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_2986_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2994_ = v_hash_3013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2995_ = 32u64;
                v___x_2996_ = lean_uint64_shift_right(v___y_2994_, v___x_2995_);
                v_fold_2997_ = lean_uint64_xor(v___y_2994_, v___x_2996_);
                v___x_2998_ = 16u64;
                v___x_2999_ = lean_uint64_shift_right(v_fold_2997_, v___x_2998_);
                v___x_3000_ = lean_uint64_xor(v_fold_2997_, v___x_2999_);
                v___x_3001_ = lean_uint64_to_usize(v___x_3000_);
                v___x_3002_ = lean_usize_of_nat(v___x_2992_);
                v___x_3003_ = 1usize;
                v___x_3004_ = lean_usize_sub(v___x_3002_, v___x_3003_);
                v___x_3005_ = lean_usize_land(v___x_3001_, v___x_3004_);
                v___x_3006_ = lean_array_uget_borrowed(v_x_2984_, v___x_3005_);
                crate::leanh::lean_inc(v___x_3006_);
                if v_isShared_2991_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2990_, 2, v___x_3006_);
                    v___x_3008_ = v___x_2990_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3011_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_key_2986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_value_2987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 2, v___x_3006_);
                    v___x_3008_ = v_reuseFailAlloc_3011_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3009_ = lean_array_uset(v_x_2984_, v___x_3005_, v___x_3008_);
                v_x_2984_ = v___x_3009_;
                v_x_2985_ = v_tail_2988_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(
    mut v_i_3015_: *mut crate::leanh::LeanObject,
    mut v_source_3016_: *mut crate::leanh::LeanObject,
    mut v_target_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v_es_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3018_ = lean_array_get_size(v_source_3016_);
                v___x_3019_ = lean_nat_dec_lt(v_i_3015_, v___x_3018_);
                if v___x_3019_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3016_);
                    crate::leanh::lean_dec(v_i_3015_);
                    return v_target_3017_;
                } else {
                    v_es_3020_ = lean_array_fget(v_source_3016_, v_i_3015_);
                    v___x_3021_ = crate::leanh::lean_box(0);
                    v_source_3022_ = lean_array_fset(v_source_3016_, v_i_3015_, v___x_3021_);
                    v_target_3023_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_3017_, v_es_3020_);
                    v___x_3024_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3025_ = lean_nat_add(v_i_3015_, v___x_3024_);
                    crate::leanh::lean_dec(v_i_3015_);
                    v_i_3015_ = v___x_3025_;
                    v_source_3016_ = v_source_3022_;
                    v_target_3017_ = v_target_3023_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(
    mut v_data_3027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3028_ = lean_array_get_size(v_data_3027_);
    v___x_3029_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3030_ = lean_nat_mul(v___x_3028_, v___x_3029_);
    v___x_3031_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3032_ = crate::leanh::lean_box(0);
    v___x_3033_ = lean_mk_array(v_nbuckets_3030_, v___x_3032_);
    v___x_3034_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_3031_, v_data_3027_, v___x_3033_);
    return v___x_3034_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(
    mut v_a_3035_: *mut crate::leanh::LeanObject,
    mut v_x_3036_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3037_: u8 = 0;
    let mut v_key_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3036_) == 0 {
                    v___x_3037_ = 0;
                    return v___x_3037_;
                } else {
                    v_key_3038_ = crate::leanh::lean_ctor_get(v_x_3036_, 0);
                    v_tail_3039_ = crate::leanh::lean_ctor_get(v_x_3036_, 2);
                    v___x_3040_ = lean_name_eq(v_key_3038_, v_a_3035_);
                    if v___x_3040_ == 0 {
                        v_x_3036_ = v_tail_3039_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3040_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(
    mut v_a_3042_: *mut crate::leanh::LeanObject,
    mut v_x_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3044_: u8 = 0;
    let mut v_r_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3044_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_3042_, v_x_3043_);
    crate::leanh::lean_dec(v_x_3043_);
    crate::leanh::lean_dec(v_a_3042_);
    v_r_3045_ = crate::leanh::lean_box((v_res_3044_) as usize);
    return v_r_3045_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(
    mut v_m_3046_: *mut crate::leanh::LeanObject,
    mut v_a_3047_: *mut crate::leanh::LeanObject,
    mut v_b_3048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3056_: u64 = 0;
    let mut v___x_3057_: u64 = 0;
    let mut v___x_3058_: u64 = 0;
    let mut v_fold_3059_: u64 = 0;
    let mut v___x_3060_: u64 = 0;
    let mut v___x_3061_: u64 = 0;
    let mut v___x_3062_: u64 = 0;
    let mut v___x_3063_: usize = 0;
    let mut v___x_3064_: usize = 0;
    let mut v___x_3065_: usize = 0;
    let mut v___x_3066_: usize = 0;
    let mut v___x_3067_: usize = 0;
    let mut v_bkt_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v_val_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u64 = 0;
    let mut v_hash_3095_: u64 = 0;
    let mut v_isSharedCheck_3096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3049_ = crate::leanh::lean_ctor_get(v_m_3046_, 0);
                v_buckets_3050_ = crate::leanh::lean_ctor_get(v_m_3046_, 1);
                v_isSharedCheck_3096_ = (!crate::leanh::lean_is_exclusive(v_m_3046_)) as u8;
                if v_isSharedCheck_3096_ == 0 {
                    v___x_3052_ = v_m_3046_;
                    v_isShared_3053_ = v_isSharedCheck_3096_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3050_);
                    crate::leanh::lean_inc(v_size_3049_);
                    crate::leanh::lean_dec(v_m_3046_);
                    v___x_3052_ = crate::leanh::lean_box(0);
                    v_isShared_3053_ = v_isSharedCheck_3096_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3054_ = lean_array_get_size(v_buckets_3050_);
                if crate::leanh::lean_obj_tag(v_a_3047_) == 0 {
                    v___x_3094_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_3056_ = v___x_3094_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3095_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_3047_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3056_ = v_hash_3095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3057_ = 32u64;
                v___x_3058_ = lean_uint64_shift_right(v___y_3056_, v___x_3057_);
                v_fold_3059_ = lean_uint64_xor(v___y_3056_, v___x_3058_);
                v___x_3060_ = 16u64;
                v___x_3061_ = lean_uint64_shift_right(v_fold_3059_, v___x_3060_);
                v___x_3062_ = lean_uint64_xor(v_fold_3059_, v___x_3061_);
                v___x_3063_ = lean_uint64_to_usize(v___x_3062_);
                v___x_3064_ = lean_usize_of_nat(v___x_3054_);
                v___x_3065_ = 1usize;
                v___x_3066_ = lean_usize_sub(v___x_3064_, v___x_3065_);
                v___x_3067_ = lean_usize_land(v___x_3063_, v___x_3066_);
                v_bkt_3068_ = lean_array_uget_borrowed(v_buckets_3050_, v___x_3067_);
                v___x_3069_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_3047_, v_bkt_3068_);
                if v___x_3069_ == 0 {
                    v___x_3070_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3071_ = lean_nat_add(v_size_3049_, v___x_3070_);
                    crate::leanh::lean_dec(v_size_3049_);
                    crate::leanh::lean_inc(v_bkt_3068_);
                    v___x_3072_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3072_, 0, v_a_3047_);
                    crate::leanh::lean_ctor_set(v___x_3072_, 1, v_b_3048_);
                    crate::leanh::lean_ctor_set(v___x_3072_, 2, v_bkt_3068_);
                    v_buckets_x27_3073_ =
                        lean_array_uset(v_buckets_3050_, v___x_3067_, v___x_3072_);
                    v___x_3074_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3075_ = lean_nat_mul(v_size_x27_3071_, v___x_3074_);
                    v___x_3076_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3077_ = lean_nat_div(v___x_3075_, v___x_3076_);
                    crate::leanh::lean_dec(v___x_3075_);
                    v___x_3078_ = lean_array_get_size(v_buckets_x27_3073_);
                    v___x_3079_ = lean_nat_dec_le(v___x_3077_, v___x_3078_);
                    crate::leanh::lean_dec(v___x_3077_);
                    if v___x_3079_ == 0 {
                        v_val_3080_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_3073_);
                        if v_isShared_3053_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3052_, 1, v_val_3080_);
                            crate::leanh::lean_ctor_set(v___x_3052_, 0, v_size_x27_3071_);
                            v___x_3082_ = v___x_3052_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3083_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3083_,
                                0,
                                v_size_x27_3071_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_val_3080_);
                            v___x_3082_ = v_reuseFailAlloc_3083_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_3053_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3052_, 1, v_buckets_x27_3073_);
                            crate::leanh::lean_ctor_set(v___x_3052_, 0, v_size_x27_3071_);
                            v___x_3085_ = v___x_3052_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3086_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3086_,
                                0,
                                v_size_x27_3071_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3086_,
                                1,
                                v_buckets_x27_3073_,
                            );
                            v___x_3085_ = v_reuseFailAlloc_3086_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3068_);
                    v___x_3087_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3088_ =
                        lean_array_uset(v_buckets_3050_, v___x_3067_, v___x_3087_);
                    v___x_3089_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_3047_, v_b_3048_, v_bkt_3068_);
                    v___x_3090_ = lean_array_uset(v_buckets_x27_3088_, v___x_3067_, v___x_3089_);
                    if v_isShared_3053_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3052_, 1, v___x_3090_);
                        v___x_3092_ = v___x_3052_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_size_3049_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3090_);
                        v___x_3092_ = v_reuseFailAlloc_3093_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3082_;
            }
            4 => {
                return v___x_3085_;
            }
            5 => {
                return v___x_3092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(
    mut v_x_3097_: *mut crate::leanh::LeanObject,
    mut v_x_3098_: *mut crate::leanh::LeanObject,
    mut v_x_3099_: *mut crate::leanh::LeanObject,
    mut v_x_3100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u8 = 0;
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3101_ = crate::leanh::lean_ctor_get(v_x_3097_, 0);
                v_vs_3102_ = crate::leanh::lean_ctor_get(v_x_3097_, 1);
                v_isSharedCheck_3126_ = (!crate::leanh::lean_is_exclusive(v_x_3097_)) as u8;
                if v_isSharedCheck_3126_ == 0 {
                    v___x_3104_ = v_x_3097_;
                    v_isShared_3105_ = v_isSharedCheck_3126_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3102_);
                    crate::leanh::lean_inc(v_ks_3101_);
                    crate::leanh::lean_dec(v_x_3097_);
                    v___x_3104_ = crate::leanh::lean_box(0);
                    v_isShared_3105_ = v_isSharedCheck_3126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3106_ = lean_array_get_size(v_ks_3101_);
                v___x_3107_ = lean_nat_dec_lt(v_x_3098_, v___x_3106_);
                if v___x_3107_ == 0 {
                    crate::leanh::lean_dec(v_x_3098_);
                    v___x_3108_ = lean_array_push(v_ks_3101_, v_x_3099_);
                    v___x_3109_ = lean_array_push(v_vs_3102_, v_x_3100_);
                    if v_isShared_3105_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3104_, 1, v___x_3109_);
                        crate::leanh::lean_ctor_set(v___x_3104_, 0, v___x_3108_);
                        v___x_3111_ = v___x_3104_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3112_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3108_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 1, v___x_3109_);
                        v___x_3111_ = v_reuseFailAlloc_3112_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3113_ = lean_array_fget_borrowed(v_ks_3101_, v_x_3098_);
                    v___x_3114_ = lean_name_eq(v_x_3099_, v_k_x27_3113_);
                    if v___x_3114_ == 0 {
                        if v_isShared_3105_ == 0 {
                            v___x_3116_ = v___x_3104_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3120_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_ks_3101_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_vs_3102_);
                            v___x_3116_ = v_reuseFailAlloc_3120_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3121_ = lean_array_fset(v_ks_3101_, v_x_3098_, v_x_3099_);
                        v___x_3122_ = lean_array_fset(v_vs_3102_, v_x_3098_, v_x_3100_);
                        crate::leanh::lean_dec(v_x_3098_);
                        if v_isShared_3105_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3104_, 1, v___x_3122_);
                            crate::leanh::lean_ctor_set(v___x_3104_, 0, v___x_3121_);
                            v___x_3124_ = v___x_3104_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3125_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3121_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 1, v___x_3122_);
                            v___x_3124_ = v_reuseFailAlloc_3125_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3111_;
            }
            3 => {
                v___x_3117_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3118_ = lean_nat_add(v_x_3098_, v___x_3117_);
                crate::leanh::lean_dec(v_x_3098_);
                v_x_3097_ = v___x_3116_;
                v_x_3098_ = v___x_3118_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(
    mut v_n_3127_: *mut crate::leanh::LeanObject,
    mut v_k_3128_: *mut crate::leanh::LeanObject,
    mut v_v_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3130_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3131_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_3127_, v___x_3130_, v_k_3128_, v_v_3129_);
    return v___x_3131_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3132_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3132_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(
    mut v_x_3133_: *mut crate::leanh::LeanObject,
    mut v_x_3134_: usize,
    mut v_x_3135_: usize,
    mut v_x_3136_: *mut crate::leanh::LeanObject,
    mut v_x_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: usize = 0;
    let mut v___x_3140_: usize = 0;
    let mut v___x_3141_: usize = 0;
    let mut v___x_3142_: usize = 0;
    let mut v_j_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v_v_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3162_: u8 = 0;
    let mut v___x_3163_: u8 = 0;
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3169_: u8 = 0;
    let mut v_node_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: usize = 0;
    let mut v___x_3175_: usize = 0;
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3180_: u8 = 0;
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut v_unused_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: u8 = 0;
    let mut v_ks_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: usize = 0;
    let mut v___x_3200_: u8 = 0;
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v_reuseFailAlloc_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3133_) == 0 {
                    v_es_3138_ = crate::leanh::lean_ctor_get(v_x_3133_, 0);
                    v___x_3139_ = 5usize;
                    v___x_3140_ = 1usize;
                    v___x_3141_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3142_ = lean_usize_land(v_x_3134_, v___x_3141_);
                    v_j_3143_ = lean_usize_to_nat(v___x_3142_);
                    v___x_3144_ = lean_array_get_size(v_es_3138_);
                    v___x_3145_ = lean_nat_dec_lt(v_j_3143_, v___x_3144_);
                    if v___x_3145_ == 0 {
                        crate::leanh::lean_dec(v_j_3143_);
                        crate::leanh::lean_dec(v_x_3137_);
                        crate::leanh::lean_dec(v_x_3136_);
                        return v_x_3133_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3138_);
                        v_isSharedCheck_3182_ = (!crate::leanh::lean_is_exclusive(v_x_3133_)) as u8;
                        if v_isSharedCheck_3182_ == 0 {
                            v_unused_3183_ = crate::leanh::lean_ctor_get(v_x_3133_, 0);
                            crate::leanh::lean_dec(v_unused_3183_);
                            v___x_3147_ = v_x_3133_;
                            v_isShared_3148_ = v_isSharedCheck_3182_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3133_);
                            v___x_3147_ = crate::leanh::lean_box(0);
                            v_isShared_3148_ = v_isSharedCheck_3182_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3184_ = crate::leanh::lean_ctor_get(v_x_3133_, 0);
                    v_vs_3185_ = crate::leanh::lean_ctor_get(v_x_3133_, 1);
                    v_isSharedCheck_3205_ = (!crate::leanh::lean_is_exclusive(v_x_3133_)) as u8;
                    if v_isSharedCheck_3205_ == 0 {
                        v___x_3187_ = v_x_3133_;
                        v_isShared_3188_ = v_isSharedCheck_3205_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3185_);
                        crate::leanh::lean_inc(v_ks_3184_);
                        crate::leanh::lean_dec(v_x_3133_);
                        v___x_3187_ = crate::leanh::lean_box(0);
                        v_isShared_3188_ = v_isSharedCheck_3205_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3149_ = lean_array_fget(v_es_3138_, v_j_3143_);
                v___x_3150_ = crate::leanh::lean_box(0);
                v_xs_x27_3151_ = lean_array_fset(v_es_3138_, v_j_3143_, v___x_3150_);
                match crate::leanh::lean_obj_tag(v_v_3149_) {
                    0 => {
                        v_key_3158_ = crate::leanh::lean_ctor_get(v_v_3149_, 0);
                        v_val_3159_ = crate::leanh::lean_ctor_get(v_v_3149_, 1);
                        v_isSharedCheck_3169_ = (!crate::leanh::lean_is_exclusive(v_v_3149_)) as u8;
                        if v_isSharedCheck_3169_ == 0 {
                            v___x_3161_ = v_v_3149_;
                            v_isShared_3162_ = v_isSharedCheck_3169_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3159_);
                            crate::leanh::lean_inc(v_key_3158_);
                            crate::leanh::lean_dec(v_v_3149_);
                            v___x_3161_ = crate::leanh::lean_box(0);
                            v_isShared_3162_ = v_isSharedCheck_3169_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3170_ = crate::leanh::lean_ctor_get(v_v_3149_, 0);
                        v_isSharedCheck_3180_ = (!crate::leanh::lean_is_exclusive(v_v_3149_)) as u8;
                        if v_isSharedCheck_3180_ == 0 {
                            v___x_3172_ = v_v_3149_;
                            v_isShared_3173_ = v_isSharedCheck_3180_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3170_);
                            crate::leanh::lean_dec(v_v_3149_);
                            v___x_3172_ = crate::leanh::lean_box(0);
                            v_isShared_3173_ = v_isSharedCheck_3180_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3181_, 0, v_x_3136_);
                        crate::leanh::lean_ctor_set(v___x_3181_, 1, v_x_3137_);
                        v___y_3153_ = v___x_3181_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3154_ = lean_array_fset(v_xs_x27_3151_, v_j_3143_, v___y_3153_);
                crate::leanh::lean_dec(v_j_3143_);
                if v_isShared_3148_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3147_, 0, v___x_3154_);
                    v___x_3156_ = v___x_3147_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3154_);
                    v___x_3156_ = v_reuseFailAlloc_3157_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3156_;
            }
            4 => {
                v___x_3163_ = lean_name_eq(v_x_3136_, v_key_3158_);
                if v___x_3163_ == 0 {
                    crate::leanh::lean_del_object(v___x_3161_);
                    v___x_3164_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3158_,
                        v_val_3159_,
                        v_x_3136_,
                        v_x_3137_,
                    );
                    v___x_3165_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3165_, 0, v___x_3164_);
                    v___y_3153_ = v___x_3165_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3159_);
                    crate::leanh::lean_dec(v_key_3158_);
                    if v_isShared_3162_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3161_, 1, v_x_3137_);
                        crate::leanh::lean_ctor_set(v___x_3161_, 0, v_x_3136_);
                        v___x_3167_ = v___x_3161_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_x_3136_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_x_3137_);
                        v___x_3167_ = v_reuseFailAlloc_3168_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3153_ = v___x_3167_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3174_ = lean_usize_shift_right(v_x_3134_, v___x_3139_);
                v___x_3175_ = lean_usize_add(v_x_3135_, v___x_3140_);
                v___x_3176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_3170_, v___x_3174_, v___x_3175_, v_x_3136_, v_x_3137_);
                if v_isShared_3173_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3172_, 0, v___x_3176_);
                    v___x_3178_ = v___x_3172_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
                    v___x_3178_ = v_reuseFailAlloc_3179_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3153_ = v___x_3178_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3188_ == 0 {
                    v___x_3190_ = v___x_3187_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_ks_3184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_vs_3185_);
                    v___x_3190_ = v_reuseFailAlloc_3204_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3191_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_3190_, v_x_3136_, v_x_3137_);
                v___x_3199_ = 7usize;
                v___x_3200_ = lean_usize_dec_le(v___x_3199_, v_x_3135_);
                if v___x_3200_ == 0 {
                    v___x_3201_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3191_);
                    v___x_3202_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3203_ = lean_nat_dec_lt(v___x_3201_, v___x_3202_);
                    crate::leanh::lean_dec(v___x_3201_);
                    v___y_3193_ = v___x_3203_;
                    state = 10;
                    continue;
                } else {
                    v___y_3193_ = v___x_3200_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3193_ == 0 {
                    v_ks_3194_ = crate::leanh::lean_ctor_get(v_newNode_3191_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3194_);
                    v_vs_3195_ = crate::leanh::lean_ctor_get(v_newNode_3191_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3195_);
                    crate::leanh::lean_dec_ref(v_newNode_3191_);
                    v___x_3196_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3197_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
                    v___x_3198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_3135_, v_ks_3194_, v_vs_3195_, v___x_3196_, v___x_3197_);
                    crate::leanh::lean_dec_ref(v_vs_3195_);
                    crate::leanh::lean_dec_ref(v_ks_3194_);
                    return v___x_3198_;
                } else {
                    return v_newNode_3191_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(
    mut v_depth_3206_: usize,
    mut v_keys_3207_: *mut crate::leanh::LeanObject,
    mut v_vals_3208_: *mut crate::leanh::LeanObject,
    mut v_i_3209_: *mut crate::leanh::LeanObject,
    mut v_entries_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: u8 = 0;
    let mut v_k_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: u64 = 0;
    let mut v_h_3217_: usize = 0;
    let mut v___x_3218_: usize = 0;
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: usize = 0;
    let mut v___x_3221_: usize = 0;
    let mut v___x_3222_: usize = 0;
    let mut v_h_3223_: usize = 0;
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u64 = 0;
    let mut v_hash_3228_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3211_ = lean_array_get_size(v_keys_3207_);
                v___x_3212_ = lean_nat_dec_lt(v_i_3209_, v___x_3211_);
                if v___x_3212_ == 0 {
                    crate::leanh::lean_dec(v_i_3209_);
                    return v_entries_3210_;
                } else {
                    v_k_3213_ = lean_array_fget_borrowed(v_keys_3207_, v_i_3209_);
                    v_v_3214_ = lean_array_fget_borrowed(v_vals_3208_, v_i_3209_);
                    if crate::leanh::lean_obj_tag(v_k_3213_) == 0 {
                        v___x_3227_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                        v___y_3216_ = v___x_3227_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3228_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_3213_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_3216_ = v_hash_3228_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_3217_ = lean_uint64_to_usize(v___y_3216_);
                v___x_3218_ = 5usize;
                v___x_3219_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3220_ = 1usize;
                v___x_3221_ = lean_usize_sub(v_depth_3206_, v___x_3220_);
                v___x_3222_ = lean_usize_mul(v___x_3218_, v___x_3221_);
                v_h_3223_ = lean_usize_shift_right(v_h_3217_, v___x_3222_);
                v___x_3224_ = lean_nat_add(v_i_3209_, v___x_3219_);
                crate::leanh::lean_dec(v_i_3209_);
                crate::leanh::lean_inc(v_v_3214_);
                crate::leanh::lean_inc(v_k_3213_);
                v___x_3225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_3210_, v_h_3223_, v_depth_3206_, v_k_3213_, v_v_3214_);
                v_i_3209_ = v___x_3224_;
                v_entries_3210_ = v___x_3225_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(
    mut v_depth_3229_: *mut crate::leanh::LeanObject,
    mut v_keys_3230_: *mut crate::leanh::LeanObject,
    mut v_vals_3231_: *mut crate::leanh::LeanObject,
    mut v_i_3232_: *mut crate::leanh::LeanObject,
    mut v_entries_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3234_: usize = 0;
    let mut v_res_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3234_ = crate::leanh::lean_unbox_usize(v_depth_3229_);
    crate::leanh::lean_dec(v_depth_3229_);
    v_res_3235_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_3234_, v_keys_3230_, v_vals_3231_, v_i_3232_, v_entries_3233_);
    crate::leanh::lean_dec_ref(v_vals_3231_);
    crate::leanh::lean_dec_ref(v_keys_3230_);
    return v_res_3235_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_x_3236_: *mut crate::leanh::LeanObject,
    mut v_x_3237_: *mut crate::leanh::LeanObject,
    mut v_x_3238_: *mut crate::leanh::LeanObject,
    mut v_x_3239_: *mut crate::leanh::LeanObject,
    mut v_x_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1474__boxed_3241_: usize = 0;
    let mut v_x_1475__boxed_3242_: usize = 0;
    let mut v_res_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1474__boxed_3241_ = crate::leanh::lean_unbox_usize(v_x_3237_);
    crate::leanh::lean_dec(v_x_3237_);
    v_x_1475__boxed_3242_ = crate::leanh::lean_unbox_usize(v_x_3238_);
    crate::leanh::lean_dec(v_x_3238_);
    v_res_3243_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_3236_, v_x_1474__boxed_3241_, v_x_1475__boxed_3242_, v_x_3239_, v_x_3240_);
    return v_res_3243_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(
    mut v_x_3244_: *mut crate::leanh::LeanObject,
    mut v_x_3245_: *mut crate::leanh::LeanObject,
    mut v_x_3246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3248_: u64 = 0;
    let mut v___x_3249_: usize = 0;
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u64 = 0;
    let mut v_hash_3253_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3245_) == 0 {
                    v___x_3252_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_3248_ = v___x_3252_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3253_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_3245_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3248_ = v_hash_3253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3249_ = lean_uint64_to_usize(v___y_3248_);
                v___x_3250_ = 1usize;
                v___x_3251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_3244_, v___x_3249_, v___x_3250_, v_x_3245_, v_x_3246_);
                return v___x_3251_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(
    mut v_x_3254_: *mut crate::leanh::LeanObject,
    mut v_x_3255_: *mut crate::leanh::LeanObject,
    mut v_x_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_3257_: u8 = 0;
    let mut v_map_u2081_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut v_map_u2081_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_3257_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_3254_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_3257_ == 0 {
                    v_map_u2081_3258_ = crate::leanh::lean_ctor_get(v_x_3254_, 0);
                    v_map_u2082_3259_ = crate::leanh::lean_ctor_get(v_x_3254_, 1);
                    v_isSharedCheck_3267_ = (!crate::leanh::lean_is_exclusive(v_x_3254_)) as u8;
                    if v_isSharedCheck_3267_ == 0 {
                        v___x_3261_ = v_x_3254_;
                        v_isShared_3262_ = v_isSharedCheck_3267_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_3259_);
                        crate::leanh::lean_inc(v_map_u2081_3258_);
                        crate::leanh::lean_dec(v_x_3254_);
                        v___x_3261_ = crate::leanh::lean_box(0);
                        v_isShared_3262_ = v_isSharedCheck_3267_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_3268_ = crate::leanh::lean_ctor_get(v_x_3254_, 0);
                    v_map_u2082_3269_ = crate::leanh::lean_ctor_get(v_x_3254_, 1);
                    v_isSharedCheck_3277_ = (!crate::leanh::lean_is_exclusive(v_x_3254_)) as u8;
                    if v_isSharedCheck_3277_ == 0 {
                        v___x_3271_ = v_x_3254_;
                        v_isShared_3272_ = v_isSharedCheck_3277_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_3269_);
                        crate::leanh::lean_inc(v_map_u2081_3268_);
                        crate::leanh::lean_dec(v_x_3254_);
                        v___x_3271_ = crate::leanh::lean_box(0);
                        v_isShared_3272_ = v_isSharedCheck_3277_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3263_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_3259_, v_x_3255_, v_x_3256_);
                if v_isShared_3262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3261_, 1, v___x_3263_);
                    v___x_3265_ = v___x_3261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3266_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_map_u2081_3258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3263_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3266_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_3257_,
                    );
                    v___x_3265_ = v_reuseFailAlloc_3266_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3265_;
            }
            3 => {
                v___x_3273_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_3268_, v_x_3255_, v_x_3256_);
                if v_isShared_3272_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3271_, 0, v___x_3273_);
                    v___x_3275_ = v___x_3271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3276_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_map_u2082_3269_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3276_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_3257_,
                    );
                    v___x_3275_ = v_reuseFailAlloc_3276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3278_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3279_ = lean_mk_empty_array_with_capacity(v___x_3278_);
    v___x_3280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3280_, 0, v___x_3279_);
    return v___x_3280_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3281_: usize = 0;
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3281_ = 5usize;
    v___x_3282_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3283_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3284_ = lean_mk_empty_array_with_capacity(v___x_3283_);
    v___x_3285_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once
        ),
        _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0,
    );
    v___x_3286_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3286_, 0, v___x_3285_);
    crate::leanh::lean_ctor_set(v___x_3286_, 1, v___x_3284_);
    crate::leanh::lean_ctor_set(v___x_3286_, 2, v___x_3282_);
    crate::leanh::lean_ctor_set(v___x_3286_, 3, v___x_3282_);
    crate::leanh::lean_ctor_set_usize(v___x_3286_, 4, v___x_3281_);
    return v___x_3286_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(
    mut v_scopedEntries_3287_: *mut crate::leanh::LeanObject,
    mut v_ns_3288_: *mut crate::leanh::LeanObject,
    mut v_b_3289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3290_ =
        l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(
            v_scopedEntries_3287_,
            v_ns_3288_,
        );
    if crate::leanh::lean_obj_tag(v___x_3290_) == 0 {
        let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3291_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once
            ),
            _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1,
        );
        v___x_3292_ = l_Lean_PersistentArray_push___redArg(v___x_3291_, v_b_3289_);
        v___x_3293_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_3287_, v_ns_3288_, v___x_3292_);
        return v___x_3293_;
    } else {
        let mut v_val_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3294_ = crate::leanh::lean_ctor_get(v___x_3290_, 0);
        crate::leanh::lean_inc(v_val_3294_);
        crate::leanh::lean_dec_ref_known(v___x_3290_, 1);
        v___x_3295_ = l_Lean_PersistentArray_push___redArg(v_val_3294_, v_b_3289_);
        v___x_3296_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_3287_, v_ns_3288_, v___x_3295_);
        return v___x_3296_;
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_ScopedEntries_insert(
    mut v_00_u03b2_3297_: *mut crate::leanh::LeanObject,
    mut v_scopedEntries_3298_: *mut crate::leanh::LeanObject,
    mut v_ns_3299_: *mut crate::leanh::LeanObject,
    mut v_b_3300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(
        v_scopedEntries_3298_,
        v_ns_3299_,
        v_b_3300_,
    );
    return v___x_3301_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(
    mut v_00_u03b2_3302_: *mut crate::leanh::LeanObject,
    mut v_x_3303_: *mut crate::leanh::LeanObject,
    mut v_x_3304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3305_ =
        l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(
            v_x_3303_, v_x_3304_,
        );
    return v___x_3305_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(
    mut v_00_u03b2_3306_: *mut crate::leanh::LeanObject,
    mut v_x_3307_: *mut crate::leanh::LeanObject,
    mut v_x_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3309_ =
        l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(
            v_00_u03b2_3306_,
            v_x_3307_,
            v_x_3308_,
        );
    crate::leanh::lean_dec(v_x_3308_);
    crate::leanh::lean_dec_ref(v_x_3307_);
    return v_res_3309_;
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(
    mut v_00_u03b2_3310_: *mut crate::leanh::LeanObject,
    mut v_x_3311_: *mut crate::leanh::LeanObject,
    mut v_x_3312_: *mut crate::leanh::LeanObject,
    mut v_x_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ =
        l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(
            v_x_3311_, v_x_3312_, v_x_3313_,
        );
    return v___x_3314_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(
    mut v_00_u03b2_3315_: *mut crate::leanh::LeanObject,
    mut v_x_3316_: *mut crate::leanh::LeanObject,
    mut v_x_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3318_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_3316_, v_x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_3319_: *mut crate::leanh::LeanObject,
    mut v_x_3320_: *mut crate::leanh::LeanObject,
    mut v_x_3321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3322_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_3319_, v_x_3320_, v_x_3321_);
    crate::leanh::lean_dec(v_x_3321_);
    crate::leanh::lean_dec_ref(v_x_3320_);
    return v_res_3322_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(
    mut v_00_u03b2_3323_: *mut crate::leanh::LeanObject,
    mut v_m_3324_: *mut crate::leanh::LeanObject,
    mut v_a_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_3324_, v_a_3325_);
    return v___x_3326_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(
    mut v_00_u03b2_3327_: *mut crate::leanh::LeanObject,
    mut v_m_3328_: *mut crate::leanh::LeanObject,
    mut v_a_3329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_3327_, v_m_3328_, v_a_3329_);
    crate::leanh::lean_dec(v_a_3329_);
    crate::leanh::lean_dec_ref(v_m_3328_);
    return v_res_3330_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(
    mut v_00_u03b2_3331_: *mut crate::leanh::LeanObject,
    mut v_x_3332_: *mut crate::leanh::LeanObject,
    mut v_x_3333_: *mut crate::leanh::LeanObject,
    mut v_x_3334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3335_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_3332_, v_x_3333_, v_x_3334_);
    return v___x_3335_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(
    mut v_00_u03b2_3336_: *mut crate::leanh::LeanObject,
    mut v_m_3337_: *mut crate::leanh::LeanObject,
    mut v_a_3338_: *mut crate::leanh::LeanObject,
    mut v_b_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3340_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_3337_, v_a_3338_, v_b_3339_);
    return v___x_3340_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3341_: *mut crate::leanh::LeanObject,
    mut v_x_3342_: *mut crate::leanh::LeanObject,
    mut v_x_3343_: usize,
    mut v_x_3344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_3342_, v_x_3343_, v_x_3344_);
    return v___x_3345_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3346_: *mut crate::leanh::LeanObject,
    mut v_x_3347_: *mut crate::leanh::LeanObject,
    mut v_x_3348_: *mut crate::leanh::LeanObject,
    mut v_x_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1782__boxed_3350_: usize = 0;
    let mut v_res_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1782__boxed_3350_ = crate::leanh::lean_unbox_usize(v_x_3348_);
    crate::leanh::lean_dec(v_x_3348_);
    v_res_3351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_3346_, v_x_3347_, v_x_1782__boxed_3350_, v_x_3349_);
    crate::leanh::lean_dec(v_x_3349_);
    crate::leanh::lean_dec_ref(v_x_3347_);
    return v_res_3351_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3352_: *mut crate::leanh::LeanObject,
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_x_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3355_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_3353_, v_x_3354_);
    return v___x_3355_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_x_3358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3359_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_3356_, v_a_3357_, v_x_3358_);
    crate::leanh::lean_dec(v_x_3358_);
    crate::leanh::lean_dec(v_a_3357_);
    return v_res_3359_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(
    mut v_00_u03b2_3360_: *mut crate::leanh::LeanObject,
    mut v_x_3361_: *mut crate::leanh::LeanObject,
    mut v_x_3362_: usize,
    mut v_x_3363_: usize,
    mut v_x_3364_: *mut crate::leanh::LeanObject,
    mut v_x_3365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_3361_, v_x_3362_, v_x_3363_, v_x_3364_, v_x_3365_);
    return v___x_3366_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_3367_: *mut crate::leanh::LeanObject,
    mut v_x_3368_: *mut crate::leanh::LeanObject,
    mut v_x_3369_: *mut crate::leanh::LeanObject,
    mut v_x_3370_: *mut crate::leanh::LeanObject,
    mut v_x_3371_: *mut crate::leanh::LeanObject,
    mut v_x_3372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1798__boxed_3373_: usize = 0;
    let mut v_x_1799__boxed_3374_: usize = 0;
    let mut v_res_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1798__boxed_3373_ = crate::leanh::lean_unbox_usize(v_x_3369_);
    crate::leanh::lean_dec(v_x_3369_);
    v_x_1799__boxed_3374_ = crate::leanh::lean_unbox_usize(v_x_3370_);
    crate::leanh::lean_dec(v_x_3370_);
    v_res_3375_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_3367_, v_x_3368_, v_x_1798__boxed_3373_, v_x_1799__boxed_3374_, v_x_3371_, v_x_3372_);
    return v_res_3375_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(
    mut v_00_u03b2_3376_: *mut crate::leanh::LeanObject,
    mut v_a_3377_: *mut crate::leanh::LeanObject,
    mut v_x_3378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3379_: u8 = 0;
    v___x_3379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_3377_, v_x_3378_);
    return v___x_3379_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(
    mut v_00_u03b2_3380_: *mut crate::leanh::LeanObject,
    mut v_a_3381_: *mut crate::leanh::LeanObject,
    mut v_x_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3383_: u8 = 0;
    let mut v_r_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3383_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_3380_, v_a_3381_, v_x_3382_);
    crate::leanh::lean_dec(v_x_3382_);
    crate::leanh::lean_dec(v_a_3381_);
    v_r_3384_ = crate::leanh::lean_box((v_res_3383_) as usize);
    return v_r_3384_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(
    mut v_00_u03b2_3385_: *mut crate::leanh::LeanObject,
    mut v_data_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_3386_);
    return v___x_3387_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(
    mut v_00_u03b2_3388_: *mut crate::leanh::LeanObject,
    mut v_a_3389_: *mut crate::leanh::LeanObject,
    mut v_b_3390_: *mut crate::leanh::LeanObject,
    mut v_x_3391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3392_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_3389_, v_b_3390_, v_x_3391_);
    return v___x_3392_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3393_: *mut crate::leanh::LeanObject,
    mut v_keys_3394_: *mut crate::leanh::LeanObject,
    mut v_vals_3395_: *mut crate::leanh::LeanObject,
    mut v_heq_3396_: *mut crate::leanh::LeanObject,
    mut v_i_3397_: *mut crate::leanh::LeanObject,
    mut v_k_3398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3394_, v_vals_3395_, v_i_3397_, v_k_3398_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3400_: *mut crate::leanh::LeanObject,
    mut v_keys_3401_: *mut crate::leanh::LeanObject,
    mut v_vals_3402_: *mut crate::leanh::LeanObject,
    mut v_heq_3403_: *mut crate::leanh::LeanObject,
    mut v_i_3404_: *mut crate::leanh::LeanObject,
    mut v_k_3405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3406_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3400_, v_keys_3401_, v_vals_3402_, v_heq_3403_, v_i_3404_, v_k_3405_);
    crate::leanh::lean_dec(v_k_3405_);
    crate::leanh::lean_dec_ref(v_vals_3402_);
    crate::leanh::lean_dec_ref(v_keys_3401_);
    return v_res_3406_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(
    mut v_00_u03b2_3407_: *mut crate::leanh::LeanObject,
    mut v_n_3408_: *mut crate::leanh::LeanObject,
    mut v_k_3409_: *mut crate::leanh::LeanObject,
    mut v_v_3410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3411_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_3408_, v_k_3409_, v_v_3410_);
    return v___x_3411_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(
    mut v_00_u03b2_3412_: *mut crate::leanh::LeanObject,
    mut v_depth_3413_: usize,
    mut v_keys_3414_: *mut crate::leanh::LeanObject,
    mut v_vals_3415_: *mut crate::leanh::LeanObject,
    mut v_heq_3416_: *mut crate::leanh::LeanObject,
    mut v_i_3417_: *mut crate::leanh::LeanObject,
    mut v_entries_3418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3419_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_3413_, v_keys_3414_, v_vals_3415_, v_i_3417_, v_entries_3418_);
    return v___x_3419_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(
    mut v_00_u03b2_3420_: *mut crate::leanh::LeanObject,
    mut v_depth_3421_: *mut crate::leanh::LeanObject,
    mut v_keys_3422_: *mut crate::leanh::LeanObject,
    mut v_vals_3423_: *mut crate::leanh::LeanObject,
    mut v_heq_3424_: *mut crate::leanh::LeanObject,
    mut v_i_3425_: *mut crate::leanh::LeanObject,
    mut v_entries_3426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3427_: usize = 0;
    let mut v_res_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3427_ = crate::leanh::lean_unbox_usize(v_depth_3421_);
    crate::leanh::lean_dec(v_depth_3421_);
    v_res_3428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_3420_, v_depth_boxed_3427_, v_keys_3422_, v_vals_3423_, v_heq_3424_, v_i_3425_, v_entries_3426_);
    crate::leanh::lean_dec_ref(v_vals_3423_);
    crate::leanh::lean_dec_ref(v_keys_3422_);
    return v_res_3428_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(
    mut v_00_u03b2_3429_: *mut crate::leanh::LeanObject,
    mut v_i_3430_: *mut crate::leanh::LeanObject,
    mut v_source_3431_: *mut crate::leanh::LeanObject,
    mut v_target_3432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_3430_, v_source_3431_, v_target_3432_);
    return v___x_3433_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(
    mut v_00_u03b2_3434_: *mut crate::leanh::LeanObject,
    mut v_x_3435_: *mut crate::leanh::LeanObject,
    mut v_x_3436_: *mut crate::leanh::LeanObject,
    mut v_x_3437_: *mut crate::leanh::LeanObject,
    mut v_x_3438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3439_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_3435_, v_x_3436_, v_x_3437_, v_x_3438_);
    return v___x_3439_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(
    mut v_00_u03b2_3440_: *mut crate::leanh::LeanObject,
    mut v_x_3441_: *mut crate::leanh::LeanObject,
    mut v_x_3442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_3441_, v_x_3442_);
    return v___x_3443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(
    mut v_descr_3444_: *mut crate::leanh::LeanObject,
    mut v_as_3445_: *mut crate::leanh::LeanObject,
    mut v_sz_3446_: usize,
    mut v_i_3447_: usize,
    mut v_b_3448_: *mut crate::leanh::LeanObject,
    mut v___y_3449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: usize = 0;
    let mut v___x_3454_: usize = 0;
    let mut v___x_3456_: u8 = 0;
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v_a_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofOLeanEntry_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addEntry_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3480_: u8 = 0;
    let mut v_a_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofOLeanEntry_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3497_: u8 = 0;
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3456_ = lean_usize_dec_lt(v_i_3447_, v_sz_3446_);
                if v___x_3456_ == 0 {
                    crate::leanh::lean_dec_ref(v_descr_3444_);
                    v___x_3457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3457_, 0, v_b_3448_);
                    return v___x_3457_;
                } else {
                    v_fst_3458_ = crate::leanh::lean_ctor_get(v_b_3448_, 0);
                    v_snd_3459_ = crate::leanh::lean_ctor_get(v_b_3448_, 1);
                    v_isSharedCheck_3498_ = (!crate::leanh::lean_is_exclusive(v_b_3448_)) as u8;
                    if v_isSharedCheck_3498_ == 0 {
                        v___x_3461_ = v_b_3448_;
                        v_isShared_3462_ = v_isSharedCheck_3498_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3459_);
                        crate::leanh::lean_inc(v_fst_3458_);
                        crate::leanh::lean_dec(v_b_3448_);
                        v___x_3461_ = crate::leanh::lean_box(0);
                        v_isShared_3462_ = v_isSharedCheck_3498_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3453_ = 1usize;
                v___x_3454_ = lean_usize_add(v_i_3447_, v___x_3453_);
                v_i_3447_ = v___x_3454_;
                v_b_3448_ = v_a_3452_;
                state = 0;
                continue;
            }
            2 => {
                v_a_3463_ = lean_array_uget_borrowed(v_as_3445_, v_i_3447_);
                if crate::leanh::lean_obj_tag(v_a_3463_) == 0 {
                    v_a_3464_ = crate::leanh::lean_ctor_get(v_a_3463_, 0);
                    v_ofOLeanEntry_3465_ = crate::leanh::lean_ctor_get(v_descr_3444_, 2);
                    v_addEntry_3466_ = crate::leanh::lean_ctor_get(v_descr_3444_, 4);
                    crate::leanh::lean_inc_ref(v_ofOLeanEntry_3465_);
                    crate::leanh::lean_inc_ref(v___y_3449_);
                    crate::leanh::lean_inc(v_a_3464_);
                    crate::leanh::lean_inc(v_fst_3458_);
                    v___x_3467_ = crate::leanh::lean_apply_4(
                        v_ofOLeanEntry_3465_,
                        v_fst_3458_,
                        v_a_3464_,
                        v___y_3449_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3467_) == 0 {
                        v_a_3468_ = crate::leanh::lean_ctor_get(v___x_3467_, 0);
                        crate::leanh::lean_inc(v_a_3468_);
                        crate::leanh::lean_dec_ref_known(v___x_3467_, 1);
                        crate::leanh::lean_inc(v_addEntry_3466_);
                        v___x_3469_ =
                            crate::leanh::lean_apply_2(v_addEntry_3466_, v_fst_3458_, v_a_3468_);
                        if v_isShared_3462_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3461_, 0, v___x_3469_);
                            v___x_3471_ = v___x_3461_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3472_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_snd_3459_);
                            v___x_3471_ = v_reuseFailAlloc_3472_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3461_);
                        crate::leanh::lean_dec(v_snd_3459_);
                        crate::leanh::lean_dec(v_fst_3458_);
                        crate::leanh::lean_dec_ref(v_descr_3444_);
                        v_a_3473_ = crate::leanh::lean_ctor_get(v___x_3467_, 0);
                        v_isSharedCheck_3480_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3467_)) as u8;
                        if v_isSharedCheck_3480_ == 0 {
                            v___x_3475_ = v___x_3467_;
                            v_isShared_3476_ = v_isSharedCheck_3480_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3473_);
                            crate::leanh::lean_dec(v___x_3467_);
                            v___x_3475_ = crate::leanh::lean_box(0);
                            v_isShared_3476_ = v_isSharedCheck_3480_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_3481_ = crate::leanh::lean_ctor_get(v_a_3463_, 0);
                    v_a_3482_ = crate::leanh::lean_ctor_get(v_a_3463_, 1);
                    v_ofOLeanEntry_3483_ = crate::leanh::lean_ctor_get(v_descr_3444_, 2);
                    crate::leanh::lean_inc_ref(v_ofOLeanEntry_3483_);
                    crate::leanh::lean_inc_ref(v___y_3449_);
                    crate::leanh::lean_inc(v_a_3482_);
                    crate::leanh::lean_inc(v_fst_3458_);
                    v___x_3484_ = crate::leanh::lean_apply_4(
                        v_ofOLeanEntry_3483_,
                        v_fst_3458_,
                        v_a_3482_,
                        v___y_3449_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3484_) == 0 {
                        v_a_3485_ = crate::leanh::lean_ctor_get(v___x_3484_, 0);
                        crate::leanh::lean_inc(v_a_3485_);
                        crate::leanh::lean_dec_ref_known(v___x_3484_, 1);
                        crate::leanh::lean_inc(v_a_3481_);
                        v___x_3486_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(
                            v_snd_3459_,
                            v_a_3481_,
                            v_a_3485_,
                        );
                        if v_isShared_3462_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3461_, 1, v___x_3486_);
                            v___x_3488_ = v___x_3461_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3489_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_fst_3458_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3486_);
                            v___x_3488_ = v_reuseFailAlloc_3489_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3461_);
                        crate::leanh::lean_dec(v_snd_3459_);
                        crate::leanh::lean_dec(v_fst_3458_);
                        crate::leanh::lean_dec_ref(v_descr_3444_);
                        v_a_3490_ = crate::leanh::lean_ctor_get(v___x_3484_, 0);
                        v_isSharedCheck_3497_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3484_)) as u8;
                        if v_isSharedCheck_3497_ == 0 {
                            v___x_3492_ = v___x_3484_;
                            v_isShared_3493_ = v_isSharedCheck_3497_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3490_);
                            crate::leanh::lean_dec(v___x_3484_);
                            v___x_3492_ = crate::leanh::lean_box(0);
                            v_isShared_3493_ = v_isSharedCheck_3497_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_3452_ = v___x_3471_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_3476_ == 0 {
                    v___x_3478_ = v___x_3475_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
                    v___x_3478_ = v_reuseFailAlloc_3479_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3478_;
            }
            6 => {
                v_a_3452_ = v___x_3488_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_3493_ == 0 {
                    v___x_3495_ = v___x_3492_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
                    v___x_3495_ = v_reuseFailAlloc_3496_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(
    mut v_descr_3499_: *mut crate::leanh::LeanObject,
    mut v_as_3500_: *mut crate::leanh::LeanObject,
    mut v_sz_3501_: *mut crate::leanh::LeanObject,
    mut v_i_3502_: *mut crate::leanh::LeanObject,
    mut v_b_3503_: *mut crate::leanh::LeanObject,
    mut v___y_3504_: *mut crate::leanh::LeanObject,
    mut v___y_3505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3506_: usize = 0;
    let mut v_i_boxed_3507_: usize = 0;
    let mut v_res_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3506_ = crate::leanh::lean_unbox_usize(v_sz_3501_);
    crate::leanh::lean_dec(v_sz_3501_);
    v_i_boxed_3507_ = crate::leanh::lean_unbox_usize(v_i_3502_);
    crate::leanh::lean_dec(v_i_3502_);
    v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_3499_, v_as_3500_, v_sz_boxed_3506_, v_i_boxed_3507_, v_b_3503_, v___y_3504_);
    crate::leanh::lean_dec_ref(v___y_3504_);
    crate::leanh::lean_dec_ref(v_as_3500_);
    return v_res_3508_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(
    mut v_descr_3509_: *mut crate::leanh::LeanObject,
    mut v_as_3510_: *mut crate::leanh::LeanObject,
    mut v_sz_3511_: usize,
    mut v_i_3512_: usize,
    mut v_b_3513_: *mut crate::leanh::LeanObject,
    mut v___y_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v_a_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3526_: usize = 0;
    let mut v___x_3527_: usize = 0;
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3534_: u8 = 0;
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: usize = 0;
    let mut v___x_3538_: usize = 0;
    let mut v_reuseFailAlloc_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3541_: u8 = 0;
    let mut v_reuseFailAlloc_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3516_ = lean_usize_dec_lt(v_i_3512_, v_sz_3511_);
                if v___x_3516_ == 0 {
                    crate::leanh::lean_dec_ref(v_descr_3509_);
                    v___x_3517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3517_, 0, v_b_3513_);
                    return v___x_3517_;
                } else {
                    v_fst_3518_ = crate::leanh::lean_ctor_get(v_b_3513_, 0);
                    v_snd_3519_ = crate::leanh::lean_ctor_get(v_b_3513_, 1);
                    v_isSharedCheck_3543_ = (!crate::leanh::lean_is_exclusive(v_b_3513_)) as u8;
                    if v_isSharedCheck_3543_ == 0 {
                        v___x_3521_ = v_b_3513_;
                        v_isShared_3522_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3519_);
                        crate::leanh::lean_inc(v_fst_3518_);
                        crate::leanh::lean_dec(v_b_3513_);
                        v___x_3521_ = crate::leanh::lean_box(0);
                        v_isShared_3522_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3523_ = lean_array_uget_borrowed(v_as_3510_, v_i_3512_);
                if v_isShared_3522_ == 0 {
                    v___x_3525_ = v___x_3521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_fst_3518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_snd_3519_);
                    v___x_3525_ = v_reuseFailAlloc_3542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_3526_ = lean_array_size(v_a_3523_);
                v___x_3527_ = 0usize;
                crate::leanh::lean_inc_ref(v_descr_3509_);
                v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_3509_, v_a_3523_, v_sz_3526_, v___x_3527_, v___x_3525_, v___y_3514_);
                if crate::leanh::lean_obj_tag(v___x_3528_) == 0 {
                    v_a_3529_ = crate::leanh::lean_ctor_get(v___x_3528_, 0);
                    crate::leanh::lean_inc(v_a_3529_);
                    crate::leanh::lean_dec_ref_known(v___x_3528_, 1);
                    v_fst_3530_ = crate::leanh::lean_ctor_get(v_a_3529_, 0);
                    v_snd_3531_ = crate::leanh::lean_ctor_get(v_a_3529_, 1);
                    v_isSharedCheck_3541_ = (!crate::leanh::lean_is_exclusive(v_a_3529_)) as u8;
                    if v_isSharedCheck_3541_ == 0 {
                        v___x_3533_ = v_a_3529_;
                        v_isShared_3534_ = v_isSharedCheck_3541_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3531_);
                        crate::leanh::lean_inc(v_fst_3530_);
                        crate::leanh::lean_dec(v_a_3529_);
                        v___x_3533_ = crate::leanh::lean_box(0);
                        v_isShared_3534_ = v_isSharedCheck_3541_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_descr_3509_);
                    return v___x_3528_;
                }
            }
            3 => {
                if v_isShared_3534_ == 0 {
                    v___x_3536_ = v___x_3533_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_fst_3530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_snd_3531_);
                    v___x_3536_ = v_reuseFailAlloc_3540_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3537_ = 1usize;
                v___x_3538_ = lean_usize_add(v_i_3512_, v___x_3537_);
                v_i_3512_ = v___x_3538_;
                v_b_3513_ = v___x_3536_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(
    mut v_descr_3544_: *mut crate::leanh::LeanObject,
    mut v_as_3545_: *mut crate::leanh::LeanObject,
    mut v_sz_3546_: *mut crate::leanh::LeanObject,
    mut v_i_3547_: *mut crate::leanh::LeanObject,
    mut v_b_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
    mut v___y_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3551_: usize = 0;
    let mut v_i_boxed_3552_: usize = 0;
    let mut v_res_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3551_ = crate::leanh::lean_unbox_usize(v_sz_3546_);
    crate::leanh::lean_dec(v_sz_3546_);
    v_i_boxed_3552_ = crate::leanh::lean_unbox_usize(v_i_3547_);
    crate::leanh::lean_dec(v_i_3547_);
    v_res_3553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_3544_, v_as_3545_, v_sz_boxed_3551_, v_i_boxed_3552_, v_b_3548_, v___y_3549_);
    crate::leanh::lean_dec_ref(v___y_3549_);
    crate::leanh::lean_dec_ref(v_as_3545_);
    return v_res_3553_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addImportedFn___redArg(
    mut v_descr_3554_: *mut crate::leanh::LeanObject,
    mut v_as_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mkInitial_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_finalizeImport_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3565_: usize = 0;
    let mut v___x_3566_: usize = 0;
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v_fst_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_a_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3593_: u8 = 0;
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3597_: u8 = 0;
    let mut v_a_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mkInitial_3558_ = crate::leanh::lean_ctor_get(v_descr_3554_, 1);
                v_finalizeImport_3559_ = crate::leanh::lean_ctor_get(v_descr_3554_, 5);
                crate::leanh::lean_inc(v_finalizeImport_3559_);
                crate::leanh::lean_inc_ref(v_mkInitial_3558_);
                v___x_3560_ =
                    crate::leanh::lean_apply_1(v_mkInitial_3558_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_3560_) == 0 {
                    v_a_3561_ = crate::leanh::lean_ctor_get(v___x_3560_, 0);
                    crate::leanh::lean_inc(v_a_3561_);
                    crate::leanh::lean_dec_ref_known(v___x_3560_, 1);
                    v___x_3562_ = 1;
                    v___x_3563_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once), _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
                    v___x_3564_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3564_, 0, v_a_3561_);
                    crate::leanh::lean_ctor_set(v___x_3564_, 1, v___x_3563_);
                    v_sz_3565_ = lean_array_size(v_as_3555_);
                    v___x_3566_ = 0usize;
                    v___x_3567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_3554_, v_as_3555_, v_sz_3565_, v___x_3566_, v___x_3564_, v_a_3556_);
                    if crate::leanh::lean_obj_tag(v___x_3567_) == 0 {
                        v_a_3568_ = crate::leanh::lean_ctor_get(v___x_3567_, 0);
                        v_isSharedCheck_3589_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3567_)) as u8;
                        if v_isSharedCheck_3589_ == 0 {
                            v___x_3570_ = v___x_3567_;
                            v_isShared_3571_ = v_isSharedCheck_3589_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3568_);
                            crate::leanh::lean_dec(v___x_3567_);
                            v___x_3570_ = crate::leanh::lean_box(0);
                            v_isShared_3571_ = v_isSharedCheck_3589_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_finalizeImport_3559_);
                        v_a_3590_ = crate::leanh::lean_ctor_get(v___x_3567_, 0);
                        v_isSharedCheck_3597_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3567_)) as u8;
                        if v_isSharedCheck_3597_ == 0 {
                            v___x_3592_ = v___x_3567_;
                            v_isShared_3593_ = v_isSharedCheck_3597_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3590_);
                            crate::leanh::lean_dec(v___x_3567_);
                            v___x_3592_ = crate::leanh::lean_box(0);
                            v_isShared_3593_ = v_isSharedCheck_3597_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_finalizeImport_3559_);
                    crate::leanh::lean_dec_ref(v_descr_3554_);
                    v_a_3598_ = crate::leanh::lean_ctor_get(v___x_3560_, 0);
                    v_isSharedCheck_3605_ = (!crate::leanh::lean_is_exclusive(v___x_3560_)) as u8;
                    if v_isSharedCheck_3605_ == 0 {
                        v___x_3600_ = v___x_3560_;
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3598_);
                        crate::leanh::lean_dec(v___x_3560_);
                        v___x_3600_ = crate::leanh::lean_box(0);
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3572_ = crate::leanh::lean_ctor_get(v_a_3568_, 0);
                v_snd_3573_ = crate::leanh::lean_ctor_get(v_a_3568_, 1);
                v_isSharedCheck_3588_ = (!crate::leanh::lean_is_exclusive(v_a_3568_)) as u8;
                if v_isSharedCheck_3588_ == 0 {
                    v___x_3575_ = v_a_3568_;
                    v_isShared_3576_ = v_isSharedCheck_3588_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3573_);
                    crate::leanh::lean_inc(v_fst_3572_);
                    crate::leanh::lean_dec(v_a_3568_);
                    v___x_3575_ = crate::leanh::lean_box(0);
                    v_isShared_3576_ = v_isSharedCheck_3588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3577_ = crate::leanh::lean_apply_1(v_finalizeImport_3559_, v_fst_3572_);
                v___x_3578_ = l_Lean_NameSet_empty;
                v___x_3579_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3579_, 0, v___x_3577_);
                crate::leanh::lean_ctor_set(v___x_3579_, 1, v___x_3578_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3579_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3562_,
                );
                v___x_3580_ = crate::leanh::lean_box(0);
                if v_isShared_3576_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3575_, 1);
                    crate::leanh::lean_ctor_set(v___x_3575_, 1, v___x_3580_);
                    crate::leanh::lean_ctor_set(v___x_3575_, 0, v___x_3579_);
                    v___x_3582_ = v___x_3575_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3587_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 1, v___x_3580_);
                    v___x_3582_ = v_reuseFailAlloc_3587_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3583_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3583_, 0, v___x_3582_);
                crate::leanh::lean_ctor_set(v___x_3583_, 1, v_snd_3573_);
                crate::leanh::lean_ctor_set(v___x_3583_, 2, v___x_3580_);
                if v_isShared_3571_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3570_, 0, v___x_3583_);
                    v___x_3585_ = v___x_3570_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
                    v___x_3585_ = v_reuseFailAlloc_3586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3585_;
            }
            5 => {
                if v_isShared_3593_ == 0 {
                    v___x_3595_ = v___x_3592_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3596_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
                    v___x_3595_ = v_reuseFailAlloc_3596_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3595_;
            }
            7 => {
                if v_isShared_3601_ == 0 {
                    v___x_3603_ = v___x_3600_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
                    v___x_3603_ = v_reuseFailAlloc_3604_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(
    mut v_descr_3606_: *mut crate::leanh::LeanObject,
    mut v_as_3607_: *mut crate::leanh::LeanObject,
    mut v_a_3608_: *mut crate::leanh::LeanObject,
    mut v_a_3609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3610_ =
        l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_3606_, v_as_3607_, v_a_3608_);
    crate::leanh::lean_dec_ref(v_a_3608_);
    crate::leanh::lean_dec_ref(v_as_3607_);
    return v_res_3610_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addImportedFn(
    mut v_00_u03b1_3611_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3612_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3613_: *mut crate::leanh::LeanObject,
    mut v_descr_3614_: *mut crate::leanh::LeanObject,
    mut v_as_3615_: *mut crate::leanh::LeanObject,
    mut v_a_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3618_ =
        l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_3614_, v_as_3615_, v_a_3616_);
    return v___x_3618_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addImportedFn___boxed(
    mut v_00_u03b1_3619_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3620_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3621_: *mut crate::leanh::LeanObject,
    mut v_descr_3622_: *mut crate::leanh::LeanObject,
    mut v_as_3623_: *mut crate::leanh::LeanObject,
    mut v_a_3624_: *mut crate::leanh::LeanObject,
    mut v_a_3625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3626_ = l_Lean_ScopedEnvExtension_addImportedFn(
        v_00_u03b1_3619_,
        v_00_u03b2_3620_,
        v_00_u03c3_3621_,
        v_descr_3622_,
        v_as_3623_,
        v_a_3624_,
    );
    crate::leanh::lean_dec_ref(v_a_3624_);
    crate::leanh::lean_dec_ref(v_as_3623_);
    return v_res_3626_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(
    mut v_00_u03b1_3627_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3628_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3629_: *mut crate::leanh::LeanObject,
    mut v_descr_3630_: *mut crate::leanh::LeanObject,
    mut v_as_3631_: *mut crate::leanh::LeanObject,
    mut v_sz_3632_: usize,
    mut v_i_3633_: usize,
    mut v_b_3634_: *mut crate::leanh::LeanObject,
    mut v___y_3635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_3630_, v_as_3631_, v_sz_3632_, v_i_3633_, v_b_3634_, v___y_3635_);
    return v___x_3637_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(
    mut v_00_u03b1_3638_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3639_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3640_: *mut crate::leanh::LeanObject,
    mut v_descr_3641_: *mut crate::leanh::LeanObject,
    mut v_as_3642_: *mut crate::leanh::LeanObject,
    mut v_sz_3643_: *mut crate::leanh::LeanObject,
    mut v_i_3644_: *mut crate::leanh::LeanObject,
    mut v_b_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3648_: usize = 0;
    let mut v_i_boxed_3649_: usize = 0;
    let mut v_res_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3648_ = crate::leanh::lean_unbox_usize(v_sz_3643_);
    crate::leanh::lean_dec(v_sz_3643_);
    v_i_boxed_3649_ = crate::leanh::lean_unbox_usize(v_i_3644_);
    crate::leanh::lean_dec(v_i_3644_);
    v_res_3650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_3638_, v_00_u03c3_3639_, v_00_u03b2_3640_, v_descr_3641_, v_as_3642_, v_sz_boxed_3648_, v_i_boxed_3649_, v_b_3645_, v___y_3646_);
    crate::leanh::lean_dec_ref(v___y_3646_);
    crate::leanh::lean_dec_ref(v_as_3642_);
    return v_res_3650_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(
    mut v_00_u03b1_3651_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3652_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3653_: *mut crate::leanh::LeanObject,
    mut v_descr_3654_: *mut crate::leanh::LeanObject,
    mut v_as_3655_: *mut crate::leanh::LeanObject,
    mut v_sz_3656_: usize,
    mut v_i_3657_: usize,
    mut v_b_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_3654_, v_as_3655_, v_sz_3656_, v_i_3657_, v_b_3658_, v___y_3659_);
    return v___x_3661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(
    mut v_00_u03b1_3662_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3663_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3664_: *mut crate::leanh::LeanObject,
    mut v_descr_3665_: *mut crate::leanh::LeanObject,
    mut v_as_3666_: *mut crate::leanh::LeanObject,
    mut v_sz_3667_: *mut crate::leanh::LeanObject,
    mut v_i_3668_: *mut crate::leanh::LeanObject,
    mut v_b_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3672_: usize = 0;
    let mut v_i_boxed_3673_: usize = 0;
    let mut v_res_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3672_ = crate::leanh::lean_unbox_usize(v_sz_3667_);
    crate::leanh::lean_dec(v_sz_3667_);
    v_i_boxed_3673_ = crate::leanh::lean_unbox_usize(v_i_3668_);
    crate::leanh::lean_dec(v_i_3668_);
    v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_3662_, v_00_u03c3_3663_, v_00_u03b2_3664_, v_descr_3665_, v_as_3666_, v_sz_boxed_3672_, v_i_boxed_3673_, v_b_3669_, v___y_3670_);
    crate::leanh::lean_dec_ref(v___y_3670_);
    crate::leanh::lean_dec_ref(v_as_3666_);
    return v_res_3674_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(
    mut v_a_3675_: *mut crate::leanh::LeanObject,
    mut v_descr_3676_: *mut crate::leanh::LeanObject,
    mut v_a_3677_: *mut crate::leanh::LeanObject,
    mut v_a_3678_: *mut crate::leanh::LeanObject,
    mut v_a_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3685_: u8 = 0;
    let mut v___y_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_3694_: u8 = 0;
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v_addEntry_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3704_: u8 = 0;
    let mut v_unused_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3678_) == 0 {
                    crate::leanh::lean_dec(v_a_3677_);
                    crate::leanh::lean_dec_ref(v_descr_3676_);
                    v___x_3680_ = l_List_reverse___redArg(v_a_3679_);
                    return v___x_3680_;
                } else {
                    v_head_3681_ = crate::leanh::lean_ctor_get(v_a_3678_, 0);
                    v_tail_3682_ = crate::leanh::lean_ctor_get(v_a_3678_, 1);
                    v_isSharedCheck_3707_ = (!crate::leanh::lean_is_exclusive(v_a_3678_)) as u8;
                    if v_isSharedCheck_3707_ == 0 {
                        v___x_3684_ = v_a_3678_;
                        v_isShared_3685_ = v_isSharedCheck_3707_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3682_);
                        crate::leanh::lean_inc(v_head_3681_);
                        crate::leanh::lean_dec(v_a_3678_);
                        v___x_3684_ = crate::leanh::lean_box(0);
                        v_isShared_3685_ = v_isSharedCheck_3707_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_state_3692_ = crate::leanh::lean_ctor_get(v_head_3681_, 0);
                v_activeScopes_3693_ = crate::leanh::lean_ctor_get(v_head_3681_, 1);
                v_delimitsLocal_3694_ = crate::leanh::lean_ctor_get_uint8(
                    v_head_3681_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v___x_3695_ = l_Lean_NameSet_contains(v_activeScopes_3693_, v_a_3675_);
                if v___x_3695_ == 0 {
                    v___y_3687_ = v_head_3681_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeScopes_3693_);
                    crate::leanh::lean_inc(v_state_3692_);
                    v_isSharedCheck_3704_ = (!crate::leanh::lean_is_exclusive(v_head_3681_)) as u8;
                    if v_isSharedCheck_3704_ == 0 {
                        v_unused_3705_ = crate::leanh::lean_ctor_get(v_head_3681_, 1);
                        crate::leanh::lean_dec(v_unused_3705_);
                        v_unused_3706_ = crate::leanh::lean_ctor_get(v_head_3681_, 0);
                        crate::leanh::lean_dec(v_unused_3706_);
                        v___x_3697_ = v_head_3681_;
                        v_isShared_3698_ = v_isSharedCheck_3704_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_head_3681_);
                        v___x_3697_ = crate::leanh::lean_box(0);
                        v_isShared_3698_ = v_isSharedCheck_3704_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3685_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3684_, 1, v_a_3679_);
                    crate::leanh::lean_ctor_set(v___x_3684_, 0, v___y_3687_);
                    v___x_3689_ = v___x_3684_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3691_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___y_3687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_a_3679_);
                    v___x_3689_ = v_reuseFailAlloc_3691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_3678_ = v_tail_3682_;
                v_a_3679_ = v___x_3689_;
                state = 0;
                continue;
            }
            4 => {
                v_addEntry_3699_ = crate::leanh::lean_ctor_get(v_descr_3676_, 4);
                crate::leanh::lean_inc(v_addEntry_3699_);
                crate::leanh::lean_inc(v_a_3677_);
                v___x_3700_ =
                    crate::leanh::lean_apply_2(v_addEntry_3699_, v_state_3692_, v_a_3677_);
                if v_isShared_3698_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3697_, 0, v___x_3700_);
                    v___x_3702_ = v___x_3697_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3703_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_activeScopes_3693_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3703_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_delimitsLocal_3694_,
                    );
                    v___x_3702_ = v_reuseFailAlloc_3703_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_3687_ = v___x_3702_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(
    mut v_a_3708_: *mut crate::leanh::LeanObject,
    mut v_descr_3709_: *mut crate::leanh::LeanObject,
    mut v_a_3710_: *mut crate::leanh::LeanObject,
    mut v_a_3711_: *mut crate::leanh::LeanObject,
    mut v_a_3712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3713_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(
        v_a_3708_,
        v_descr_3709_,
        v_a_3710_,
        v_a_3711_,
        v_a_3712_,
    );
    crate::leanh::lean_dec(v_a_3708_);
    return v_res_3713_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(
    mut v_descr_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
    mut v_a_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v_addEntry_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_3727_: u8 = 0;
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3730_: u8 = 0;
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut v_isSharedCheck_3740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3716_) == 0 {
                    crate::leanh::lean_dec(v_a_3715_);
                    crate::leanh::lean_dec_ref(v_descr_3714_);
                    v___x_3718_ = l_List_reverse___redArg(v_a_3717_);
                    return v___x_3718_;
                } else {
                    v_head_3719_ = crate::leanh::lean_ctor_get(v_a_3716_, 0);
                    v_tail_3720_ = crate::leanh::lean_ctor_get(v_a_3716_, 1);
                    v_isSharedCheck_3740_ = (!crate::leanh::lean_is_exclusive(v_a_3716_)) as u8;
                    if v_isSharedCheck_3740_ == 0 {
                        v___x_3722_ = v_a_3716_;
                        v_isShared_3723_ = v_isSharedCheck_3740_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3720_);
                        crate::leanh::lean_inc(v_head_3719_);
                        crate::leanh::lean_dec(v_a_3716_);
                        v___x_3722_ = crate::leanh::lean_box(0);
                        v_isShared_3723_ = v_isSharedCheck_3740_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_3724_ = crate::leanh::lean_ctor_get(v_descr_3714_, 4);
                v_state_3725_ = crate::leanh::lean_ctor_get(v_head_3719_, 0);
                v_activeScopes_3726_ = crate::leanh::lean_ctor_get(v_head_3719_, 1);
                v_delimitsLocal_3727_ = crate::leanh::lean_ctor_get_uint8(
                    v_head_3719_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_3739_ = (!crate::leanh::lean_is_exclusive(v_head_3719_)) as u8;
                if v_isSharedCheck_3739_ == 0 {
                    v___x_3729_ = v_head_3719_;
                    v_isShared_3730_ = v_isSharedCheck_3739_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeScopes_3726_);
                    crate::leanh::lean_inc(v_state_3725_);
                    crate::leanh::lean_dec(v_head_3719_);
                    v___x_3729_ = crate::leanh::lean_box(0);
                    v_isShared_3730_ = v_isSharedCheck_3739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_addEntry_3724_);
                crate::leanh::lean_inc(v_a_3715_);
                v___x_3731_ =
                    crate::leanh::lean_apply_2(v_addEntry_3724_, v_state_3725_, v_a_3715_);
                if v_isShared_3730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3729_, 0, v___x_3731_);
                    v___x_3733_ = v___x_3729_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3738_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_activeScopes_3726_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3738_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_delimitsLocal_3727_,
                    );
                    v___x_3733_ = v_reuseFailAlloc_3738_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3723_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3722_, 1, v_a_3717_);
                    crate::leanh::lean_ctor_set(v___x_3722_, 0, v___x_3733_);
                    v___x_3735_ = v___x_3722_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_a_3717_);
                    v___x_3735_ = v_reuseFailAlloc_3737_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3716_ = v_tail_3720_;
                v_a_3717_ = v___x_3735_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addEntryFn___redArg(
    mut v_descr_3741_: *mut crate::leanh::LeanObject,
    mut v_s_3742_: *mut crate::leanh::LeanObject,
    mut v_e_3743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stateStack_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v_a_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3753_: u8 = 0;
    let mut v_toOLeanEntry_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3765_: u8 = 0;
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v_stateStack_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3772_: u8 = 0;
    let mut v_a_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v_toOLeanEntry_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut v_isSharedCheck_3791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_3743_) == 0 {
                    v_stateStack_3744_ = crate::leanh::lean_ctor_get(v_s_3742_, 0);
                    v_scopedEntries_3745_ = crate::leanh::lean_ctor_get(v_s_3742_, 1);
                    v_newEntries_3746_ = crate::leanh::lean_ctor_get(v_s_3742_, 2);
                    v_isSharedCheck_3766_ = (!crate::leanh::lean_is_exclusive(v_s_3742_)) as u8;
                    if v_isSharedCheck_3766_ == 0 {
                        v___x_3748_ = v_s_3742_;
                        v_isShared_3749_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_newEntries_3746_);
                        crate::leanh::lean_inc(v_scopedEntries_3745_);
                        crate::leanh::lean_inc(v_stateStack_3744_);
                        crate::leanh::lean_dec(v_s_3742_);
                        v___x_3748_ = crate::leanh::lean_box(0);
                        v_isShared_3749_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_stateStack_3767_ = crate::leanh::lean_ctor_get(v_s_3742_, 0);
                    v_scopedEntries_3768_ = crate::leanh::lean_ctor_get(v_s_3742_, 1);
                    v_newEntries_3769_ = crate::leanh::lean_ctor_get(v_s_3742_, 2);
                    v_isSharedCheck_3791_ = (!crate::leanh::lean_is_exclusive(v_s_3742_)) as u8;
                    if v_isSharedCheck_3791_ == 0 {
                        v___x_3771_ = v_s_3742_;
                        v_isShared_3772_ = v_isSharedCheck_3791_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_newEntries_3769_);
                        crate::leanh::lean_inc(v_scopedEntries_3768_);
                        crate::leanh::lean_inc(v_stateStack_3767_);
                        crate::leanh::lean_dec(v_s_3742_);
                        v___x_3771_ = crate::leanh::lean_box(0);
                        v_isShared_3772_ = v_isSharedCheck_3791_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3750_ = crate::leanh::lean_ctor_get(v_e_3743_, 0);
                v_isSharedCheck_3765_ = (!crate::leanh::lean_is_exclusive(v_e_3743_)) as u8;
                if v_isSharedCheck_3765_ == 0 {
                    v___x_3752_ = v_e_3743_;
                    v_isShared_3753_ = v_isSharedCheck_3765_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3750_);
                    crate::leanh::lean_dec(v_e_3743_);
                    v___x_3752_ = crate::leanh::lean_box(0);
                    v_isShared_3753_ = v_isSharedCheck_3765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toOLeanEntry_3754_ = crate::leanh::lean_ctor_get(v_descr_3741_, 3);
                crate::leanh::lean_inc(v_toOLeanEntry_3754_);
                v___x_3755_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_a_3750_);
                v___x_3756_ =
                    l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(
                        v_descr_3741_,
                        v_a_3750_,
                        v_stateStack_3744_,
                        v___x_3755_,
                    );
                v___x_3757_ = crate::leanh::lean_apply_1(v_toOLeanEntry_3754_, v_a_3750_);
                if v_isShared_3753_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3752_, 0, v___x_3757_);
                    v___x_3759_ = v___x_3752_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3757_);
                    v___x_3759_ = v_reuseFailAlloc_3764_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3760_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3760_, 0, v___x_3759_);
                crate::leanh::lean_ctor_set(v___x_3760_, 1, v_newEntries_3746_);
                if v_isShared_3749_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3748_, 2, v___x_3760_);
                    crate::leanh::lean_ctor_set(v___x_3748_, 0, v___x_3756_);
                    v___x_3762_ = v___x_3748_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3763_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_scopedEntries_3745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3763_, 2, v___x_3760_);
                    v___x_3762_ = v_reuseFailAlloc_3763_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3762_;
            }
            5 => {
                v_a_3773_ = crate::leanh::lean_ctor_get(v_e_3743_, 0);
                v_a_3774_ = crate::leanh::lean_ctor_get(v_e_3743_, 1);
                v_isSharedCheck_3790_ = (!crate::leanh::lean_is_exclusive(v_e_3743_)) as u8;
                if v_isSharedCheck_3790_ == 0 {
                    v___x_3776_ = v_e_3743_;
                    v_isShared_3777_ = v_isSharedCheck_3790_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3774_);
                    crate::leanh::lean_inc(v_a_3773_);
                    crate::leanh::lean_dec(v_e_3743_);
                    v___x_3776_ = crate::leanh::lean_box(0);
                    v_isShared_3777_ = v_isSharedCheck_3790_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_toOLeanEntry_3778_ = crate::leanh::lean_ctor_get(v_descr_3741_, 3);
                crate::leanh::lean_inc(v_toOLeanEntry_3778_);
                v___x_3779_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_a_3774_, 2);
                v___x_3780_ =
                    l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(
                        v_a_3773_,
                        v_descr_3741_,
                        v_a_3774_,
                        v_stateStack_3767_,
                        v___x_3779_,
                    );
                crate::leanh::lean_inc(v_a_3773_);
                v___x_3781_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(
                    v_scopedEntries_3768_,
                    v_a_3773_,
                    v_a_3774_,
                );
                v___x_3782_ = crate::leanh::lean_apply_1(v_toOLeanEntry_3778_, v_a_3774_);
                if v_isShared_3777_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3776_, 1, v___x_3782_);
                    v___x_3784_ = v___x_3776_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3789_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 1, v___x_3782_);
                    v___x_3784_ = v_reuseFailAlloc_3789_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3785_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3785_, 0, v___x_3784_);
                crate::leanh::lean_ctor_set(v___x_3785_, 1, v_newEntries_3769_);
                if v_isShared_3772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3771_, 2, v___x_3785_);
                    crate::leanh::lean_ctor_set(v___x_3771_, 1, v___x_3781_);
                    crate::leanh::lean_ctor_set(v___x_3771_, 0, v___x_3780_);
                    v___x_3787_ = v___x_3771_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3788_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 1, v___x_3781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 2, v___x_3785_);
                    v___x_3787_ = v_reuseFailAlloc_3788_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addEntryFn(
    mut v_00_u03b1_3792_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3793_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3794_: *mut crate::leanh::LeanObject,
    mut v_descr_3795_: *mut crate::leanh::LeanObject,
    mut v_s_3796_: *mut crate::leanh::LeanObject,
    mut v_e_3797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3798_ =
        l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_3795_, v_s_3796_, v_e_3797_);
    return v___x_3798_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(
    mut v_00_u03c3_3799_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3800_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3801_: *mut crate::leanh::LeanObject,
    mut v_descr_3802_: *mut crate::leanh::LeanObject,
    mut v_a_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
    mut v_a_3805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3806_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(
        v_descr_3802_,
        v_a_3803_,
        v_a_3804_,
        v_a_3805_,
    );
    return v___x_3806_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(
    mut v_00_u03c3_3807_: *mut crate::leanh::LeanObject,
    mut v_a_3808_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3809_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3810_: *mut crate::leanh::LeanObject,
    mut v_descr_3811_: *mut crate::leanh::LeanObject,
    mut v_a_3812_: *mut crate::leanh::LeanObject,
    mut v_a_3813_: *mut crate::leanh::LeanObject,
    mut v_a_3814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3815_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(
        v_a_3808_,
        v_descr_3811_,
        v_a_3812_,
        v_a_3813_,
        v_a_3814_,
    );
    return v___x_3815_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(
    mut v_00_u03c3_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3818_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3819_: *mut crate::leanh::LeanObject,
    mut v_descr_3820_: *mut crate::leanh::LeanObject,
    mut v_a_3821_: *mut crate::leanh::LeanObject,
    mut v_a_3822_: *mut crate::leanh::LeanObject,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3824_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(
        v_00_u03c3_3816_,
        v_a_3817_,
        v_00_u03b2_3818_,
        v_00_u03b1_3819_,
        v_descr_3820_,
        v_a_3821_,
        v_a_3822_,
        v_a_3823_,
    );
    crate::leanh::lean_dec(v_a_3817_);
    return v_res_3824_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(
    mut v_descr_3825_: *mut crate::leanh::LeanObject,
    mut v_env_3826_: *mut crate::leanh::LeanObject,
    mut v_as_3827_: *mut crate::leanh::LeanObject,
    mut v_sz_3828_: usize,
    mut v_i_3829_: usize,
    mut v_b_3830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: usize = 0;
    let mut v___x_3834_: usize = 0;
    let mut v___x_3836_: u8 = 0;
    let mut v_snd_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3841_: u8 = 0;
    let mut v_fst_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3846_: u8 = 0;
    let mut v_a_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v_exportEntry_x3f_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_server_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_private_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_server_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3882_: u8 = 0;
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v_val_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut v_a_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v_exportEntry_x3f_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_server_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_private_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_server_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut v_isSharedCheck_3938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3836_ = lean_usize_dec_lt(v_i_3829_, v_sz_3828_);
                if v___x_3836_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_3826_);
                    crate::leanh::lean_dec_ref(v_descr_3825_);
                    return v_b_3830_;
                } else {
                    v_snd_3837_ = crate::leanh::lean_ctor_get(v_b_3830_, 1);
                    v_fst_3838_ = crate::leanh::lean_ctor_get(v_b_3830_, 0);
                    v_isSharedCheck_3938_ = (!crate::leanh::lean_is_exclusive(v_b_3830_)) as u8;
                    if v_isSharedCheck_3938_ == 0 {
                        v___x_3840_ = v_b_3830_;
                        v_isShared_3841_ = v_isSharedCheck_3938_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3837_);
                        crate::leanh::lean_inc(v_fst_3838_);
                        crate::leanh::lean_dec(v_b_3830_);
                        v___x_3840_ = crate::leanh::lean_box(0);
                        v_isShared_3841_ = v_isSharedCheck_3938_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3833_ = 1usize;
                v___x_3834_ = lean_usize_add(v_i_3829_, v___x_3833_);
                v_i_3829_ = v___x_3834_;
                v_b_3830_ = v_a_3832_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_3842_ = crate::leanh::lean_ctor_get(v_snd_3837_, 0);
                v_snd_3843_ = crate::leanh::lean_ctor_get(v_snd_3837_, 1);
                v_isSharedCheck_3937_ = (!crate::leanh::lean_is_exclusive(v_snd_3837_)) as u8;
                if v_isSharedCheck_3937_ == 0 {
                    v___x_3845_ = v_snd_3837_;
                    v_isShared_3846_ = v_isSharedCheck_3937_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3843_);
                    crate::leanh::lean_inc(v_fst_3842_);
                    crate::leanh::lean_dec(v_snd_3837_);
                    v___x_3845_ = crate::leanh::lean_box(0);
                    v_isShared_3846_ = v_isSharedCheck_3937_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_3847_ = lean_array_uget(v_as_3827_, v_i_3829_);
                if crate::leanh::lean_obj_tag(v_a_3847_) == 0 {
                    v_a_3848_ = crate::leanh::lean_ctor_get(v_a_3847_, 0);
                    v_isSharedCheck_3897_ = (!crate::leanh::lean_is_exclusive(v_a_3847_)) as u8;
                    if v_isSharedCheck_3897_ == 0 {
                        v___x_3850_ = v_a_3847_;
                        v_isShared_3851_ = v_isSharedCheck_3897_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3848_);
                        crate::leanh::lean_dec(v_a_3847_);
                        v___x_3850_ = crate::leanh::lean_box(0);
                        v_isShared_3851_ = v_isSharedCheck_3897_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_3898_ = crate::leanh::lean_ctor_get(v_a_3847_, 0);
                    v_a_3899_ = crate::leanh::lean_ctor_get(v_a_3847_, 1);
                    v_isSharedCheck_3936_ = (!crate::leanh::lean_is_exclusive(v_a_3847_)) as u8;
                    if v_isSharedCheck_3936_ == 0 {
                        v___x_3901_ = v_a_3847_;
                        v_isShared_3902_ = v_isSharedCheck_3936_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3899_);
                        crate::leanh::lean_inc(v_a_3898_);
                        crate::leanh::lean_dec(v_a_3847_);
                        v___x_3901_ = crate::leanh::lean_box(0);
                        v_isShared_3902_ = v_isSharedCheck_3936_;
                        state = 16;
                        continue;
                    }
                }
            }
            4 => {
                v_exportEntry_x3f_3852_ = crate::leanh::lean_ctor_get(v_descr_3825_, 6);
                crate::leanh::lean_inc_ref(v_exportEntry_x3f_3852_);
                crate::leanh::lean_inc_ref(v_env_3826_);
                v___x_3853_ =
                    crate::leanh::lean_apply_2(v_exportEntry_x3f_3852_, v_env_3826_, v_a_3848_);
                v_exported_3854_ = crate::leanh::lean_ctor_get(v___x_3853_, 0);
                crate::leanh::lean_inc(v_exported_3854_);
                v_server_3855_ = crate::leanh::lean_ctor_get(v___x_3853_, 1);
                crate::leanh::lean_inc(v_server_3855_);
                v_private_3856_ = crate::leanh::lean_ctor_get(v___x_3853_, 2);
                crate::leanh::lean_inc(v_private_3856_);
                crate::leanh::lean_dec_ref(v___x_3853_);
                if crate::leanh::lean_obj_tag(v_exported_3854_) == 1 {
                    v_val_3888_ = crate::leanh::lean_ctor_get(v_exported_3854_, 0);
                    v_isSharedCheck_3896_ =
                        (!crate::leanh::lean_is_exclusive(v_exported_3854_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v___x_3890_ = v_exported_3854_;
                        v_isShared_3891_ = v_isSharedCheck_3896_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3888_);
                        crate::leanh::lean_dec(v_exported_3854_);
                        v___x_3890_ = crate::leanh::lean_box(0);
                        v_isShared_3891_ = v_isSharedCheck_3896_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_exported_3854_);
                    v_exported_3878_ = v_fst_3838_;
                    state = 11;
                    continue;
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_private_3856_) == 1 {
                    v_val_3860_ = crate::leanh::lean_ctor_get(v_private_3856_, 0);
                    crate::leanh::lean_inc(v_val_3860_);
                    crate::leanh::lean_dec_ref_known(v_private_3856_, 1);
                    if v_isShared_3851_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3850_, 0, v_val_3860_);
                        v___x_3862_ = v___x_3850_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_val_3860_);
                        v___x_3862_ = v_reuseFailAlloc_3870_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_private_3856_);
                    crate::leanh::lean_del_object(v___x_3850_);
                    if v_isShared_3846_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3845_, 0, v_server_3859_);
                        v___x_3872_ = v___x_3845_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3876_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_server_3859_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_snd_3843_);
                        v___x_3872_ = v_reuseFailAlloc_3876_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3863_ = lean_array_push(v_snd_3843_, v___x_3862_);
                if v_isShared_3846_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3845_, 1, v___x_3863_);
                    crate::leanh::lean_ctor_set(v___x_3845_, 0, v_server_3859_);
                    v___x_3865_ = v___x_3845_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_server_3859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3869_, 1, v___x_3863_);
                    v___x_3865_ = v_reuseFailAlloc_3869_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3841_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3840_, 1, v___x_3865_);
                    crate::leanh::lean_ctor_set(v___x_3840_, 0, v___y_3858_);
                    v___x_3867_ = v___x_3840_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3868_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___y_3858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3865_);
                    v___x_3867_ = v_reuseFailAlloc_3868_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_3832_ = v___x_3867_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_3841_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3840_, 1, v___x_3872_);
                    crate::leanh::lean_ctor_set(v___x_3840_, 0, v___y_3858_);
                    v___x_3874_ = v___x_3840_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___y_3858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3875_, 1, v___x_3872_);
                    v___x_3874_ = v_reuseFailAlloc_3875_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_3832_ = v___x_3874_;
                state = 1;
                continue;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_server_3855_) == 1 {
                    v_val_3879_ = crate::leanh::lean_ctor_get(v_server_3855_, 0);
                    v_isSharedCheck_3887_ =
                        (!crate::leanh::lean_is_exclusive(v_server_3855_)) as u8;
                    if v_isSharedCheck_3887_ == 0 {
                        v___x_3881_ = v_server_3855_;
                        v_isShared_3882_ = v_isSharedCheck_3887_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3879_);
                        crate::leanh::lean_dec(v_server_3855_);
                        v___x_3881_ = crate::leanh::lean_box(0);
                        v_isShared_3882_ = v_isSharedCheck_3887_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_server_3855_);
                    v___y_3858_ = v_exported_3878_;
                    v_server_3859_ = v_fst_3842_;
                    state = 5;
                    continue;
                }
            }
            12 => {
                if v_isShared_3882_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3881_, 0);
                    v___x_3884_ = v___x_3881_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_val_3879_);
                    v___x_3884_ = v_reuseFailAlloc_3886_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_3885_ = lean_array_push(v_fst_3842_, v___x_3884_);
                v___y_3858_ = v_exported_3878_;
                v_server_3859_ = v___x_3885_;
                state = 5;
                continue;
            }
            14 => {
                if v_isShared_3891_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3890_, 0);
                    v___x_3893_ = v___x_3890_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_val_3888_);
                    v___x_3893_ = v_reuseFailAlloc_3895_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3894_ = lean_array_push(v_fst_3838_, v___x_3893_);
                v_exported_3878_ = v___x_3894_;
                state = 11;
                continue;
            }
            16 => {
                v_exportEntry_x3f_3903_ = crate::leanh::lean_ctor_get(v_descr_3825_, 6);
                crate::leanh::lean_inc_ref(v_exportEntry_x3f_3903_);
                crate::leanh::lean_inc_ref(v_env_3826_);
                v___x_3904_ =
                    crate::leanh::lean_apply_2(v_exportEntry_x3f_3903_, v_env_3826_, v_a_3899_);
                v_exported_3905_ = crate::leanh::lean_ctor_get(v___x_3904_, 0);
                crate::leanh::lean_inc(v_exported_3905_);
                v_server_3906_ = crate::leanh::lean_ctor_get(v___x_3904_, 1);
                crate::leanh::lean_inc(v_server_3906_);
                v_private_3907_ = crate::leanh::lean_ctor_get(v___x_3904_, 2);
                crate::leanh::lean_inc(v_private_3907_);
                crate::leanh::lean_dec_ref(v___x_3904_);
                if crate::leanh::lean_obj_tag(v_exported_3905_) == 1 {
                    v_val_3933_ = crate::leanh::lean_ctor_get(v_exported_3905_, 0);
                    crate::leanh::lean_inc(v_val_3933_);
                    crate::leanh::lean_dec_ref_known(v_exported_3905_, 1);
                    crate::leanh::lean_inc(v_a_3898_);
                    v___x_3934_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3934_, 0, v_a_3898_);
                    crate::leanh::lean_ctor_set(v___x_3934_, 1, v_val_3933_);
                    v___x_3935_ = lean_array_push(v_fst_3838_, v___x_3934_);
                    v_exported_3929_ = v___x_3935_;
                    state = 23;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_exported_3905_);
                    v_exported_3929_ = v_fst_3838_;
                    state = 23;
                    continue;
                }
            }
            17 => {
                if crate::leanh::lean_obj_tag(v_private_3907_) == 1 {
                    v_val_3911_ = crate::leanh::lean_ctor_get(v_private_3907_, 0);
                    crate::leanh::lean_inc(v_val_3911_);
                    crate::leanh::lean_dec_ref_known(v_private_3907_, 1);
                    if v_isShared_3902_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3901_, 1, v_val_3911_);
                        v___x_3913_ = v___x_3901_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3921_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3898_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_val_3911_);
                        v___x_3913_ = v_reuseFailAlloc_3921_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_private_3907_);
                    crate::leanh::lean_del_object(v___x_3901_);
                    crate::leanh::lean_dec(v_a_3898_);
                    if v_isShared_3846_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3845_, 0, v_server_3910_);
                        v___x_3923_ = v___x_3845_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_3927_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_server_3910_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_snd_3843_);
                        v___x_3923_ = v_reuseFailAlloc_3927_;
                        state = 21;
                        continue;
                    }
                }
            }
            18 => {
                v___x_3914_ = lean_array_push(v_snd_3843_, v___x_3913_);
                if v_isShared_3846_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3845_, 1, v___x_3914_);
                    crate::leanh::lean_ctor_set(v___x_3845_, 0, v_server_3910_);
                    v___x_3916_ = v___x_3845_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3920_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_server_3910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 1, v___x_3914_);
                    v___x_3916_ = v_reuseFailAlloc_3920_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3841_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3840_, 1, v___x_3916_);
                    crate::leanh::lean_ctor_set(v___x_3840_, 0, v___y_3909_);
                    v___x_3918_ = v___x_3840_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___y_3909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3919_, 1, v___x_3916_);
                    v___x_3918_ = v_reuseFailAlloc_3919_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v_a_3832_ = v___x_3918_;
                state = 1;
                continue;
            }
            21 => {
                if v_isShared_3841_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3840_, 1, v___x_3923_);
                    crate::leanh::lean_ctor_set(v___x_3840_, 0, v___y_3909_);
                    v___x_3925_ = v___x_3840_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3926_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___y_3909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 1, v___x_3923_);
                    v___x_3925_ = v_reuseFailAlloc_3926_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v_a_3832_ = v___x_3925_;
                state = 1;
                continue;
            }
            23 => {
                if crate::leanh::lean_obj_tag(v_server_3906_) == 1 {
                    v_val_3930_ = crate::leanh::lean_ctor_get(v_server_3906_, 0);
                    crate::leanh::lean_inc(v_val_3930_);
                    crate::leanh::lean_dec_ref_known(v_server_3906_, 1);
                    crate::leanh::lean_inc(v_a_3898_);
                    v___x_3931_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3931_, 0, v_a_3898_);
                    crate::leanh::lean_ctor_set(v___x_3931_, 1, v_val_3930_);
                    v___x_3932_ = lean_array_push(v_fst_3842_, v___x_3931_);
                    v___y_3909_ = v_exported_3929_;
                    v_server_3910_ = v___x_3932_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_server_3906_);
                    v___y_3909_ = v_exported_3929_;
                    v_server_3910_ = v_fst_3842_;
                    state = 17;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(
    mut v_descr_3939_: *mut crate::leanh::LeanObject,
    mut v_env_3940_: *mut crate::leanh::LeanObject,
    mut v_as_3941_: *mut crate::leanh::LeanObject,
    mut v_sz_3942_: *mut crate::leanh::LeanObject,
    mut v_i_3943_: *mut crate::leanh::LeanObject,
    mut v_b_3944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3945_: usize = 0;
    let mut v_i_boxed_3946_: usize = 0;
    let mut v_res_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3945_ = crate::leanh::lean_unbox_usize(v_sz_3942_);
    crate::leanh::lean_dec(v_sz_3942_);
    v_i_boxed_3946_ = crate::leanh::lean_unbox_usize(v_i_3943_);
    crate::leanh::lean_dec(v_i_3943_);
    v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_3939_, v_env_3940_, v_as_3941_, v_sz_boxed_3945_, v_i_boxed_3946_, v_b_3944_);
    crate::leanh::lean_dec_ref(v_as_3941_);
    return v_res_3947_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(
    mut v_descr_3955_: *mut crate::leanh::LeanObject,
    mut v_env_3956_: *mut crate::leanh::LeanObject,
    mut v_s_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_newEntries_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3961_: u8 = 0;
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3965_: usize = 0;
    let mut v___x_3966_: usize = 0;
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3975_: u8 = 0;
    let mut v_unused_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_newEntries_3958_ = crate::leanh::lean_ctor_get(v_s_3957_, 2);
                v_isSharedCheck_3975_ = (!crate::leanh::lean_is_exclusive(v_s_3957_)) as u8;
                if v_isSharedCheck_3975_ == 0 {
                    v_unused_3976_ = crate::leanh::lean_ctor_get(v_s_3957_, 1);
                    crate::leanh::lean_dec(v_unused_3976_);
                    v_unused_3977_ = crate::leanh::lean_ctor_get(v_s_3957_, 0);
                    crate::leanh::lean_dec(v_unused_3977_);
                    v___x_3960_ = v_s_3957_;
                    v_isShared_3961_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_newEntries_3958_);
                    crate::leanh::lean_dec(v_s_3957_);
                    v___x_3960_ = crate::leanh::lean_box(0);
                    v_isShared_3961_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3962_ = lean_array_mk(v_newEntries_3958_);
                v___x_3963_ = l_Array_reverse___redArg(v___x_3962_);
                v___x_3964_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2;
                v_sz_3965_ = lean_array_size(v___x_3963_);
                v___x_3966_ = 0usize;
                v___x_3967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_3955_, v_env_3956_, v___x_3963_, v_sz_3965_, v___x_3966_, v___x_3964_);
                crate::leanh::lean_dec_ref(v___x_3963_);
                v_snd_3968_ = crate::leanh::lean_ctor_get(v___x_3967_, 1);
                crate::leanh::lean_inc(v_snd_3968_);
                v_fst_3969_ = crate::leanh::lean_ctor_get(v___x_3967_, 0);
                crate::leanh::lean_inc(v_fst_3969_);
                crate::leanh::lean_dec_ref(v___x_3967_);
                v_fst_3970_ = crate::leanh::lean_ctor_get(v_snd_3968_, 0);
                crate::leanh::lean_inc(v_fst_3970_);
                v_snd_3971_ = crate::leanh::lean_ctor_get(v_snd_3968_, 1);
                crate::leanh::lean_inc(v_snd_3971_);
                crate::leanh::lean_dec(v_snd_3968_);
                if v_isShared_3961_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3960_, 2, v_snd_3971_);
                    crate::leanh::lean_ctor_set(v___x_3960_, 1, v_fst_3970_);
                    crate::leanh::lean_ctor_set(v___x_3960_, 0, v_fst_3969_);
                    v___x_3973_ = v___x_3960_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3974_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_fst_3969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_fst_3970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_snd_3971_);
                    v___x_3973_ = v_reuseFailAlloc_3974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_exportEntriesFn(
    mut v_00_u03b1_3978_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3979_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3980_: *mut crate::leanh::LeanObject,
    mut v_descr_3981_: *mut crate::leanh::LeanObject,
    mut v_env_3982_: *mut crate::leanh::LeanObject,
    mut v_s_3983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3984_ =
        l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_3981_, v_env_3982_, v_s_3983_);
    return v___x_3984_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(
    mut v_00_u03b1_3985_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3986_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3987_: *mut crate::leanh::LeanObject,
    mut v_descr_3988_: *mut crate::leanh::LeanObject,
    mut v_env_3989_: *mut crate::leanh::LeanObject,
    mut v_as_3990_: *mut crate::leanh::LeanObject,
    mut v_sz_3991_: usize,
    mut v_i_3992_: usize,
    mut v_b_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_3988_, v_env_3989_, v_as_3990_, v_sz_3991_, v_i_3992_, v_b_3993_);
    return v___x_3994_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(
    mut v_00_u03b1_3995_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3996_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_3997_: *mut crate::leanh::LeanObject,
    mut v_descr_3998_: *mut crate::leanh::LeanObject,
    mut v_env_3999_: *mut crate::leanh::LeanObject,
    mut v_as_4000_: *mut crate::leanh::LeanObject,
    mut v_sz_4001_: *mut crate::leanh::LeanObject,
    mut v_i_4002_: *mut crate::leanh::LeanObject,
    mut v_b_4003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4004_: usize = 0;
    let mut v_i_boxed_4005_: usize = 0;
    let mut v_res_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4004_ = crate::leanh::lean_unbox_usize(v_sz_4001_);
    crate::leanh::lean_dec(v_sz_4001_);
    v_i_boxed_4005_ = crate::leanh::lean_unbox_usize(v_i_4002_);
    crate::leanh::lean_dec(v_i_4002_);
    v_res_4006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_3995_, v_00_u03b2_3996_, v_00_u03c3_3997_, v_descr_3998_, v_env_3999_, v_as_4000_, v_sz_boxed_4004_, v_i_boxed_4005_, v_b_4003_);
    crate::leanh::lean_dec_ref(v_as_4000_);
    return v_res_4006_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(
    mut v_x_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4010_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1;
    v___x_4011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4011_, 0, v___x_4010_);
    return v___x_4011_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(
    mut v_x_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4015_ =
        l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_4012_, v___y_4013_);
    crate::leanh::lean_dec_ref(v___y_4013_);
    crate::leanh::lean_dec_ref(v_x_4012_);
    return v_res_4015_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(
    mut v_s_4016_: *mut crate::leanh::LeanObject,
    mut v_x_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_4016_);
    return v_s_4016_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(
    mut v_s_4018_: *mut crate::leanh::LeanObject,
    mut v_x_4019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4020_ =
        l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_4018_, v_x_4019_);
    crate::leanh::lean_dec_ref(v_x_4019_);
    crate::leanh::lean_dec_ref(v_s_4018_);
    return v_res_4020_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(
    mut v_x_4023_: *mut crate::leanh::LeanObject,
    mut v_x_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4025_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0;
    return v___x_4025_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(
    mut v_x_4026_: *mut crate::leanh::LeanObject,
    mut v_x_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4028_ =
        l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_4026_, v_x_4027_);
    crate::leanh::lean_dec_ref(v_x_4027_);
    crate::leanh::lean_dec_ref(v_x_4026_);
    return v_res_4028_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(
    mut v_x_4029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4030_ = crate::leanh::lean_box(0);
    return v___x_4030_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(
    mut v_x_4031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4032_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_4031_);
    crate::leanh::lean_dec_ref(v_x_4031_);
    return v_res_4032_;
}
pub unsafe fn _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_Lean_instInhabitedEnvExtension_default(crate::leanh::lean_box(0));
    return v___x_4037_;
}
pub unsafe fn _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4038_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3;
    v___f_4039_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2;
    v___f_4040_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1;
    v___f_4041_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0;
    v___x_4042_ = crate::leanh::lean_box(0);
    v___x_4043_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once
        ),
        _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4,
    );
    v___x_4044_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4044_, 0, v___x_4043_);
    crate::leanh::lean_ctor_set(v___x_4044_, 1, v___x_4042_);
    crate::leanh::lean_ctor_set(v___x_4044_, 2, v___f_4041_);
    crate::leanh::lean_ctor_set(v___x_4044_, 3, v___f_4040_);
    crate::leanh::lean_ctor_set(v___x_4044_, 4, v___f_4039_);
    crate::leanh::lean_ctor_set(v___x_4044_, 5, v___f_4038_);
    return v___x_4044_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg(
    mut v_inst_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4046_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0;
    v___f_4047_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4047_, 0, v_inst_4045_);
    v___f_4048_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1;
    v___f_4049_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2;
    v___x_4050_ = crate::leanh::lean_box(0);
    v___x_4051_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3,
    );
    v___x_4052_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4;
    v___x_4053_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4053_, 0, v___x_4050_);
    crate::leanh::lean_ctor_set(v___x_4053_, 1, v___x_4051_);
    crate::leanh::lean_ctor_set(v___x_4053_, 2, v___f_4046_);
    crate::leanh::lean_ctor_set(v___x_4053_, 3, v___f_4047_);
    crate::leanh::lean_ctor_set(v___x_4053_, 4, v___f_4048_);
    crate::leanh::lean_ctor_set(v___x_4053_, 5, v___x_4052_);
    crate::leanh::lean_ctor_set(v___x_4053_, 6, v___f_4049_);
    v___x_4054_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once
        ),
        _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5,
    );
    v___x_4055_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4055_, 0, v___x_4053_);
    crate::leanh::lean_ctor_set(v___x_4055_, 1, v___x_4054_);
    return v___x_4055_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default(
    mut v_00_u03b1_4056_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4057_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4058_: *mut crate::leanh::LeanObject,
    mut v_inst_4059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4060_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_4059_);
    return v___x_4060_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension___redArg(
    mut v_inst_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4062_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_4061_);
    return v___x_4062_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension(
    mut v_a_4063_: *mut crate::leanh::LeanObject,
    mut v_inst_4064_: *mut crate::leanh::LeanObject,
    mut v_a_4065_: *mut crate::leanh::LeanObject,
    mut v_a_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4067_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_4064_);
    return v___x_4067_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4071_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_;
    v___x_4072_ = lean_st_mk_ref(v___x_4071_);
    v___x_4073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4073_, 0, v___x_4072_);
    return v___x_4073_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(
    mut v_a_4074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4075_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
    return v_res_4075_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(
    mut v_s_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_newEntries_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_newEntries_4080_ = crate::leanh::lean_ctor_get(v_s_4079_, 2);
    v___x_4081_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1;
    v___x_4082_ = l_List_lengthTR___redArg(v_newEntries_4080_);
    v___x_4083_ = l_Nat_reprFast(v___x_4082_);
    v___x_4084_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4084_, 0, v___x_4083_);
    v___x_4085_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4085_, 0, v___x_4081_);
    crate::leanh::lean_ctor_set(v___x_4085_, 1, v___x_4084_);
    return v___x_4085_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(
    mut v_s_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4087_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_4086_);
    crate::leanh::lean_dec_ref(v_s_4086_);
    return v_res_4087_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(
    mut v_x_4088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4089_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0;
    return v___x_4089_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(
    mut v_x_4090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4091_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_4090_);
    crate::leanh::lean_dec_ref(v_x_4090_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg(
    mut v_descr_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4111_: u8 = 0;
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4120_: u8 = 0;
    let mut v_a_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_4096_ = crate::leanh::lean_ctor_get(v_descr_4094_, 0);
                v___f_4097_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0;
                v___f_4098_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1;
                crate::leanh::lean_inc_ref_n(v_descr_4094_, 4);
                v___x_4099_ = crate::leanh::lean_alloc_closure(
                    l_Lean_ScopedEnvExtension_mkInitial___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_4099_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4099_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4099_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4099_, 3, v_descr_4094_);
                v___x_4100_ = crate::leanh::lean_alloc_closure(
                    l_Lean_ScopedEnvExtension_addImportedFn___boxed as *mut core::ffi::c_void,
                    7,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_4100_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4100_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4100_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4100_, 3, v_descr_4094_);
                v___x_4101_ = crate::leanh::lean_alloc_closure(
                    l_Lean_ScopedEnvExtension_addEntryFn as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_4101_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4101_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4101_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4101_, 3, v_descr_4094_);
                v___x_4102_ = crate::leanh::lean_alloc_closure(
                    l_Lean_ScopedEnvExtension_exportEntriesFn as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_4102_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4102_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4102_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4102_, 3, v_descr_4094_);
                v___x_4103_ = crate::leanh::lean_box(2);
                v___x_4104_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_name_4096_);
                v___x_4105_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4105_, 0, v_name_4096_);
                crate::leanh::lean_ctor_set(v___x_4105_, 1, v___x_4099_);
                crate::leanh::lean_ctor_set(v___x_4105_, 2, v___x_4100_);
                crate::leanh::lean_ctor_set(v___x_4105_, 3, v___x_4101_);
                crate::leanh::lean_ctor_set(v___x_4105_, 4, v___x_4102_);
                crate::leanh::lean_ctor_set(v___x_4105_, 5, v___f_4097_);
                crate::leanh::lean_ctor_set(v___x_4105_, 6, v___x_4103_);
                crate::leanh::lean_ctor_set(v___x_4105_, 7, v___x_4104_);
                v___x_4106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4106_, 0, v___x_4105_);
                crate::leanh::lean_ctor_set(v___x_4106_, 1, v___f_4098_);
                v___x_4107_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4106_);
                if crate::leanh::lean_obj_tag(v___x_4107_) == 0 {
                    v_a_4108_ = crate::leanh::lean_ctor_get(v___x_4107_, 0);
                    v_isSharedCheck_4120_ = (!crate::leanh::lean_is_exclusive(v___x_4107_)) as u8;
                    if v_isSharedCheck_4120_ == 0 {
                        v___x_4110_ = v___x_4107_;
                        v_isShared_4111_ = v_isSharedCheck_4120_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4108_);
                        crate::leanh::lean_dec(v___x_4107_);
                        v___x_4110_ = crate::leanh::lean_box(0);
                        v_isShared_4111_ = v_isSharedCheck_4120_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_descr_4094_);
                    v_a_4121_ = crate::leanh::lean_ctor_get(v___x_4107_, 0);
                    v_isSharedCheck_4128_ = (!crate::leanh::lean_is_exclusive(v___x_4107_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4123_ = v___x_4107_;
                        v_isShared_4124_ = v_isSharedCheck_4128_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4121_);
                        crate::leanh::lean_dec(v___x_4107_);
                        v___x_4123_ = crate::leanh::lean_box(0);
                        v_isShared_4124_ = v_isSharedCheck_4128_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4112_ = l_Lean_scopedEnvExtensionsRef;
                v___x_4113_ = lean_st_ref_take(v___x_4112_);
                v___x_4114_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4114_, 0, v_descr_4094_);
                crate::leanh::lean_ctor_set(v___x_4114_, 1, v_a_4108_);
                crate::leanh::lean_inc_ref(v___x_4114_);
                v___x_4115_ = lean_array_push(v___x_4113_, v___x_4114_);
                v___x_4116_ = lean_st_ref_set(v___x_4112_, v___x_4115_);
                if v_isShared_4111_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4110_, 0, v___x_4114_);
                    v___x_4118_ = v___x_4110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4119_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4114_);
                    v___x_4118_ = v_reuseFailAlloc_4119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4118_;
            }
            3 => {
                if v_isShared_4124_ == 0 {
                    v___x_4126_ = v___x_4123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
                    v___x_4126_ = v_reuseFailAlloc_4127_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4126_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(
    mut v_descr_4129_: *mut crate::leanh::LeanObject,
    mut v_a_4130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4131_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_4129_);
    return v_res_4131_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe(
    mut v_00_u03b1_4132_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4133_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4134_: *mut crate::leanh::LeanObject,
    mut v_descr_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_4135_);
    return v___x_4137_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___boxed(
    mut v_00_u03b1_4138_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4139_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4140_: *mut crate::leanh::LeanObject,
    mut v_descr_4141_: *mut crate::leanh::LeanObject,
    mut v_a_4142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4143_ = l_Lean_registerScopedEnvExtensionUnsafe(
        v_00_u03b1_4138_,
        v_00_u03b2_4139_,
        v_00_u03c3_4140_,
        v_descr_4141_,
    );
    return v_res_4143_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(
    mut v_s_4144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stateStack_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v_state_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4156_: u8 = 0;
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4165_: u8 = 0;
    let mut v_isSharedCheck_4166_: u8 = 0;
    let mut v_unused_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4145_ = crate::leanh::lean_ctor_get(v_s_4144_, 0);
                if crate::leanh::lean_obj_tag(v_stateStack_4145_) == 0 {
                    return v_s_4144_;
                } else {
                    crate::leanh::lean_inc_ref(v_stateStack_4145_);
                    v_head_4146_ = crate::leanh::lean_ctor_get(v_stateStack_4145_, 0);
                    crate::leanh::lean_inc(v_head_4146_);
                    v_scopedEntries_4147_ = crate::leanh::lean_ctor_get(v_s_4144_, 1);
                    v_newEntries_4148_ = crate::leanh::lean_ctor_get(v_s_4144_, 2);
                    v_isSharedCheck_4166_ = (!crate::leanh::lean_is_exclusive(v_s_4144_)) as u8;
                    if v_isSharedCheck_4166_ == 0 {
                        v_unused_4167_ = crate::leanh::lean_ctor_get(v_s_4144_, 0);
                        crate::leanh::lean_dec(v_unused_4167_);
                        v___x_4150_ = v_s_4144_;
                        v_isShared_4151_ = v_isSharedCheck_4166_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_newEntries_4148_);
                        crate::leanh::lean_inc(v_scopedEntries_4147_);
                        crate::leanh::lean_dec(v_s_4144_);
                        v___x_4150_ = crate::leanh::lean_box(0);
                        v_isShared_4151_ = v_isSharedCheck_4166_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_state_4152_ = crate::leanh::lean_ctor_get(v_head_4146_, 0);
                v_activeScopes_4153_ = crate::leanh::lean_ctor_get(v_head_4146_, 1);
                v_isSharedCheck_4165_ = (!crate::leanh::lean_is_exclusive(v_head_4146_)) as u8;
                if v_isSharedCheck_4165_ == 0 {
                    v___x_4155_ = v_head_4146_;
                    v_isShared_4156_ = v_isSharedCheck_4165_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeScopes_4153_);
                    crate::leanh::lean_inc(v_state_4152_);
                    crate::leanh::lean_dec(v_head_4146_);
                    v___x_4155_ = crate::leanh::lean_box(0);
                    v_isShared_4156_ = v_isSharedCheck_4165_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4157_ = 1;
                if v_isShared_4156_ == 0 {
                    v___x_4159_ = v___x_4155_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4164_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_state_4152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 1, v_activeScopes_4153_);
                    v___x_4159_ = v_reuseFailAlloc_4164_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4159_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4157_,
                );
                v___x_4160_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4160_, 0, v___x_4159_);
                crate::leanh::lean_ctor_set(v___x_4160_, 1, v_stateStack_4145_);
                if v_isShared_4151_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4150_, 0, v___x_4160_);
                    v___x_4162_ = v___x_4150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_scopedEntries_4147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 2, v_newEntries_4148_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_pushScope___redArg(
    mut v_ext_4169_: *mut crate::leanh::LeanObject,
    mut v_env_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ext_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ext_4171_ = crate::leanh::lean_ctor_get(v_ext_4169_, 1);
    crate::leanh::lean_inc_ref(v_ext_4171_);
    crate::leanh::lean_dec_ref(v_ext_4169_);
    v___f_4172_ = l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0;
    v___x_4173_ = crate::leanh::lean_box(1);
    v___x_4174_ = crate::leanh::lean_box(0);
    v___x_4175_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4171_,
        v_env_4170_,
        v___f_4172_,
        v___x_4173_,
        v___x_4174_,
    );
    return v___x_4175_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_pushScope(
    mut v_00_u03b1_4176_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4177_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4178_: *mut crate::leanh::LeanObject,
    mut v_ext_4179_: *mut crate::leanh::LeanObject,
    mut v_env_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4181_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_4179_, v_env_4180_);
    return v___x_4181_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(
    mut v_s_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stateStack_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4193_: u8 = 0;
    let mut v_unused_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4183_ = crate::leanh::lean_ctor_get(v_s_4182_, 0);
                if crate::leanh::lean_obj_tag(v_stateStack_4183_) == 1 {
                    v_tail_4184_ = crate::leanh::lean_ctor_get(v_stateStack_4183_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_4184_) == 1 {
                        crate::leanh::lean_inc_ref(v_tail_4184_);
                        v_scopedEntries_4185_ = crate::leanh::lean_ctor_get(v_s_4182_, 1);
                        v_newEntries_4186_ = crate::leanh::lean_ctor_get(v_s_4182_, 2);
                        v_isSharedCheck_4193_ = (!crate::leanh::lean_is_exclusive(v_s_4182_)) as u8;
                        if v_isSharedCheck_4193_ == 0 {
                            v_unused_4194_ = crate::leanh::lean_ctor_get(v_s_4182_, 0);
                            crate::leanh::lean_dec(v_unused_4194_);
                            v___x_4188_ = v_s_4182_;
                            v_isShared_4189_ = v_isSharedCheck_4193_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_newEntries_4186_);
                            crate::leanh::lean_inc(v_scopedEntries_4185_);
                            crate::leanh::lean_dec(v_s_4182_);
                            v___x_4188_ = crate::leanh::lean_box(0);
                            v_isShared_4189_ = v_isSharedCheck_4193_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v_s_4182_;
                    }
                } else {
                    return v_s_4182_;
                }
            }
            1 => {
                if v_isShared_4189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4188_, 0, v_tail_4184_);
                    v___x_4191_ = v___x_4188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4192_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_tail_4184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_scopedEntries_4185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_newEntries_4186_);
                    v___x_4191_ = v_reuseFailAlloc_4192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_popScope___redArg(
    mut v_ext_4196_: *mut crate::leanh::LeanObject,
    mut v_env_4197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ext_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ext_4198_ = crate::leanh::lean_ctor_get(v_ext_4196_, 1);
    crate::leanh::lean_inc_ref(v_ext_4198_);
    crate::leanh::lean_dec_ref(v_ext_4196_);
    v___f_4199_ = l_Lean_ScopedEnvExtension_popScope___redArg___closed__0;
    v___x_4200_ = crate::leanh::lean_box(1);
    v___x_4201_ = crate::leanh::lean_box(0);
    v___x_4202_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4198_,
        v_env_4197_,
        v___f_4199_,
        v___x_4200_,
        v___x_4201_,
    );
    return v___x_4202_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_popScope(
    mut v_00_u03b1_4203_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4204_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4205_: *mut crate::leanh::LeanObject,
    mut v_ext_4206_: *mut crate::leanh::LeanObject,
    mut v_env_4207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4208_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_4206_, v_env_4207_);
    return v___x_4208_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4212_: u8 = 0;
    let mut v_head_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v_state_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4222_: u8 = 0;
    let mut v_one_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4232_: u8 = 0;
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4211_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4212_ = lean_nat_dec_eq(v_a_4209_, v_zero_4211_);
                if v_isZero_4212_ == 1 {
                    return v_a_4210_;
                } else {
                    if crate::leanh::lean_obj_tag(v_a_4210_) == 0 {
                        return v_a_4210_;
                    } else {
                        v_head_4213_ = crate::leanh::lean_ctor_get(v_a_4210_, 0);
                        v_tail_4214_ = crate::leanh::lean_ctor_get(v_a_4210_, 1);
                        v_isSharedCheck_4233_ = (!crate::leanh::lean_is_exclusive(v_a_4210_)) as u8;
                        if v_isSharedCheck_4233_ == 0 {
                            v___x_4216_ = v_a_4210_;
                            v_isShared_4217_ = v_isSharedCheck_4233_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_4214_);
                            crate::leanh::lean_inc(v_head_4213_);
                            crate::leanh::lean_dec(v_a_4210_);
                            v___x_4216_ = crate::leanh::lean_box(0);
                            v_isShared_4217_ = v_isSharedCheck_4233_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_state_4218_ = crate::leanh::lean_ctor_get(v_head_4213_, 0);
                v_activeScopes_4219_ = crate::leanh::lean_ctor_get(v_head_4213_, 1);
                v_isSharedCheck_4232_ = (!crate::leanh::lean_is_exclusive(v_head_4213_)) as u8;
                if v_isSharedCheck_4232_ == 0 {
                    v___x_4221_ = v_head_4213_;
                    v_isShared_4222_ = v_isSharedCheck_4232_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeScopes_4219_);
                    crate::leanh::lean_inc(v_state_4218_);
                    crate::leanh::lean_dec(v_head_4213_);
                    v___x_4221_ = crate::leanh::lean_box(0);
                    v_isShared_4222_ = v_isSharedCheck_4232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_one_4223_ = crate::leanh::lean_unsigned_to_nat(1);
                v_n_4224_ = lean_nat_sub(v_a_4209_, v_one_4223_);
                if v_isShared_4222_ == 0 {
                    v___x_4226_ = v___x_4221_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_state_4218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_activeScopes_4219_);
                    v___x_4226_ = v_reuseFailAlloc_4231_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4226_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v_isZero_4212_,
                );
                v___x_4227_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_4224_, v_tail_4214_);
                crate::leanh::lean_dec(v_n_4224_);
                if v_isShared_4217_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4216_, 1, v___x_4227_);
                    crate::leanh::lean_ctor_set(v___x_4216_, 0, v___x_4226_);
                    v___x_4229_ = v___x_4216_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4230_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4227_);
                    v___x_4229_ = v_reuseFailAlloc_4230_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(
    mut v_a_4234_: *mut crate::leanh::LeanObject,
    mut v_a_4235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4236_ =
        l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(
            v_a_4234_, v_a_4235_,
        );
    crate::leanh::lean_dec(v_a_4234_);
    return v_res_4236_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(
    mut v_00_u03c3_4237_: *mut crate::leanh::LeanObject,
    mut v_a_4238_: *mut crate::leanh::LeanObject,
    mut v_a_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4240_ =
        l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(
            v_a_4238_, v_a_4239_,
        );
    return v___x_4240_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(
    mut v_00_u03c3_4241_: *mut crate::leanh::LeanObject,
    mut v_a_4242_: *mut crate::leanh::LeanObject,
    mut v_a_4243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4244_ =
        l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(
            v_00_u03c3_4241_,
            v_a_4242_,
            v_a_4243_,
        );
    crate::leanh::lean_dec(v_a_4242_);
    return v_res_4244_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(
    mut v_depth_4245_: *mut crate::leanh::LeanObject,
    mut v_s_4246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stateStack_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4252_: u8 = 0;
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4247_ = crate::leanh::lean_ctor_get(v_s_4246_, 0);
                v_scopedEntries_4248_ = crate::leanh::lean_ctor_get(v_s_4246_, 1);
                v_newEntries_4249_ = crate::leanh::lean_ctor_get(v_s_4246_, 2);
                v_isSharedCheck_4257_ = (!crate::leanh::lean_is_exclusive(v_s_4246_)) as u8;
                if v_isSharedCheck_4257_ == 0 {
                    v___x_4251_ = v_s_4246_;
                    v_isShared_4252_ = v_isSharedCheck_4257_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_newEntries_4249_);
                    crate::leanh::lean_inc(v_scopedEntries_4248_);
                    crate::leanh::lean_inc(v_stateStack_4247_);
                    crate::leanh::lean_dec(v_s_4246_);
                    v___x_4251_ = crate::leanh::lean_box(0);
                    v_isShared_4252_ = v_isSharedCheck_4257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4253_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_4245_, v_stateStack_4247_);
                if v_isShared_4252_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4251_, 0, v___x_4253_);
                    v___x_4255_ = v___x_4251_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4256_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 1, v_scopedEntries_4248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 2, v_newEntries_4249_);
                    v___x_4255_ = v_reuseFailAlloc_4256_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(
    mut v_depth_4258_: *mut crate::leanh::LeanObject,
    mut v_s_4259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4260_ =
        l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_4258_, v_s_4259_);
    crate::leanh::lean_dec(v_depth_4258_);
    return v_res_4260_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(
    mut v_ext_4261_: *mut crate::leanh::LeanObject,
    mut v_env_4262_: *mut crate::leanh::LeanObject,
    mut v_depth_4263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ext_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ext_4264_ = crate::leanh::lean_ctor_get(v_ext_4261_, 1);
    crate::leanh::lean_inc_ref(v_ext_4264_);
    crate::leanh::lean_dec_ref(v_ext_4261_);
    v___f_4265_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4265_, 0, v_depth_4263_);
    v___x_4266_ = crate::leanh::lean_box(1);
    v___x_4267_ = crate::leanh::lean_box(0);
    v___x_4268_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4264_,
        v_env_4262_,
        v___f_4265_,
        v___x_4266_,
        v___x_4267_,
    );
    return v___x_4268_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_setDelimitsLocal(
    mut v_00_u03b1_4269_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4270_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4271_: *mut crate::leanh::LeanObject,
    mut v_ext_4272_: *mut crate::leanh::LeanObject,
    mut v_env_4273_: *mut crate::leanh::LeanObject,
    mut v_depth_4274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4275_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(
        v_ext_4272_,
        v_env_4273_,
        v_depth_4274_,
    );
    return v___x_4275_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addEntry___redArg(
    mut v_ext_4276_: *mut crate::leanh::LeanObject,
    mut v_env_4277_: *mut crate::leanh::LeanObject,
    mut v_b_4278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ext_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ext_4279_ = crate::leanh::lean_ctor_get(v_ext_4276_, 1);
    crate::leanh::lean_inc_ref(v_ext_4279_);
    crate::leanh::lean_dec_ref(v_ext_4276_);
    v_toEnvExtension_4280_ = crate::leanh::lean_ctor_get(v_ext_4279_, 0);
    v_asyncMode_4281_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4280_, 2);
    crate::leanh::lean_inc(v_asyncMode_4281_);
    v___x_4282_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4282_, 0, v_b_4278_);
    v___x_4283_ = crate::leanh::lean_box(0);
    v___x_4284_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v_ext_4279_,
        v_env_4277_,
        v___x_4282_,
        v_asyncMode_4281_,
        v___x_4283_,
    );
    crate::leanh::lean_dec(v_asyncMode_4281_);
    return v___x_4284_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addEntry(
    mut v_00_u03b1_4285_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4286_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4287_: *mut crate::leanh::LeanObject,
    mut v_ext_4288_: *mut crate::leanh::LeanObject,
    mut v_env_4289_: *mut crate::leanh::LeanObject,
    mut v_b_4290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_4288_, v_env_4289_, v_b_4290_);
    return v___x_4291_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addScopedEntry___redArg(
    mut v_ext_4292_: *mut crate::leanh::LeanObject,
    mut v_env_4293_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_4294_: *mut crate::leanh::LeanObject,
    mut v_b_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ext_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4299_: u8 = 0;
    let mut v_toEnvExtension_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4307_: u8 = 0;
    let mut v_unused_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ext_4296_ = crate::leanh::lean_ctor_get(v_ext_4292_, 1);
                v_isSharedCheck_4307_ = (!crate::leanh::lean_is_exclusive(v_ext_4292_)) as u8;
                if v_isSharedCheck_4307_ == 0 {
                    v_unused_4308_ = crate::leanh::lean_ctor_get(v_ext_4292_, 0);
                    crate::leanh::lean_dec(v_unused_4308_);
                    v___x_4298_ = v_ext_4292_;
                    v_isShared_4299_ = v_isSharedCheck_4307_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ext_4296_);
                    crate::leanh::lean_dec(v_ext_4292_);
                    v___x_4298_ = crate::leanh::lean_box(0);
                    v_isShared_4299_ = v_isSharedCheck_4307_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toEnvExtension_4300_ = crate::leanh::lean_ctor_get(v_ext_4296_, 0);
                v_asyncMode_4301_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4300_, 2);
                crate::leanh::lean_inc(v_asyncMode_4301_);
                if v_isShared_4299_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4298_, 1);
                    crate::leanh::lean_ctor_set(v___x_4298_, 1, v_b_4295_);
                    crate::leanh::lean_ctor_set(v___x_4298_, 0, v_namespaceName_4294_);
                    v___x_4303_ = v___x_4298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4306_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_namespaceName_4294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 1, v_b_4295_);
                    v___x_4303_ = v_reuseFailAlloc_4306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4304_ = crate::leanh::lean_box(0);
                v___x_4305_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_ext_4296_,
                    v_env_4293_,
                    v___x_4303_,
                    v_asyncMode_4301_,
                    v___x_4304_,
                );
                crate::leanh::lean_dec(v_asyncMode_4301_);
                return v___x_4305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addScopedEntry(
    mut v_00_u03b1_4309_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4310_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4311_: *mut crate::leanh::LeanObject,
    mut v_ext_4312_: *mut crate::leanh::LeanObject,
    mut v_env_4313_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_4314_: *mut crate::leanh::LeanObject,
    mut v_b_4315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4316_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(
        v_ext_4312_,
        v_env_4313_,
        v_namespaceName_4314_,
        v_b_4315_,
    );
    return v___x_4316_;
}
pub unsafe fn l_Lean_stateStackModify___redArg(
    mut v_ext_4317_: *mut crate::leanh::LeanObject,
    mut v_states_4318_: *mut crate::leanh::LeanObject,
    mut v_b_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_descr_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v_addEntry_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_4329_: u8 = 0;
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_top_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4344_: u8 = 0;
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_states_4318_) == 0 {
                    crate::leanh::lean_dec(v_b_4319_);
                    crate::leanh::lean_dec_ref(v_ext_4317_);
                    return v_states_4318_;
                } else {
                    v_descr_4320_ = crate::leanh::lean_ctor_get(v_ext_4317_, 0);
                    v_head_4321_ = crate::leanh::lean_ctor_get(v_states_4318_, 0);
                    v_tail_4322_ = crate::leanh::lean_ctor_get(v_states_4318_, 1);
                    v_isSharedCheck_4345_ =
                        (!crate::leanh::lean_is_exclusive(v_states_4318_)) as u8;
                    if v_isSharedCheck_4345_ == 0 {
                        v___x_4324_ = v_states_4318_;
                        v_isShared_4325_ = v_isSharedCheck_4345_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4322_);
                        crate::leanh::lean_inc(v_head_4321_);
                        crate::leanh::lean_dec(v_states_4318_);
                        v___x_4324_ = crate::leanh::lean_box(0);
                        v_isShared_4325_ = v_isSharedCheck_4345_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4326_ = crate::leanh::lean_ctor_get(v_descr_4320_, 4);
                v_state_4327_ = crate::leanh::lean_ctor_get(v_head_4321_, 0);
                v_activeScopes_4328_ = crate::leanh::lean_ctor_get(v_head_4321_, 1);
                v_delimitsLocal_4329_ = crate::leanh::lean_ctor_get_uint8(
                    v_head_4321_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_4344_ = (!crate::leanh::lean_is_exclusive(v_head_4321_)) as u8;
                if v_isSharedCheck_4344_ == 0 {
                    v___x_4331_ = v_head_4321_;
                    v_isShared_4332_ = v_isSharedCheck_4344_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeScopes_4328_);
                    crate::leanh::lean_inc(v_state_4327_);
                    crate::leanh::lean_dec(v_head_4321_);
                    v___x_4331_ = crate::leanh::lean_box(0);
                    v_isShared_4332_ = v_isSharedCheck_4344_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_addEntry_4326_);
                crate::leanh::lean_inc(v_b_4319_);
                v___x_4333_ =
                    crate::leanh::lean_apply_2(v_addEntry_4326_, v_state_4327_, v_b_4319_);
                if v_isShared_4332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4331_, 0, v___x_4333_);
                    v_top_4335_ = v___x_4331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4343_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_activeScopes_4328_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4343_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_delimitsLocal_4329_,
                    );
                    v_top_4335_ = v_reuseFailAlloc_4343_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_delimitsLocal_4329_ == 0 {
                    v___x_4336_ =
                        l_Lean_stateStackModify___redArg(v_ext_4317_, v_tail_4322_, v_b_4319_);
                    if v_isShared_4325_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4324_, 1, v___x_4336_);
                        crate::leanh::lean_ctor_set(v___x_4324_, 0, v_top_4335_);
                        v___x_4338_ = v___x_4324_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4339_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_top_4335_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4339_, 1, v___x_4336_);
                        v___x_4338_ = v_reuseFailAlloc_4339_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_4319_);
                    crate::leanh::lean_dec_ref(v_ext_4317_);
                    if v_isShared_4325_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4324_, 0, v_top_4335_);
                        v___x_4341_ = v___x_4324_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4342_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_top_4335_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4342_, 1, v_tail_4322_);
                        v___x_4341_ = v_reuseFailAlloc_4342_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4338_;
            }
            5 => {
                return v___x_4341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_stateStackModify(
    mut v_00_u03b1_4346_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4347_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4348_: *mut crate::leanh::LeanObject,
    mut v_ext_4349_: *mut crate::leanh::LeanObject,
    mut v_states_4350_: *mut crate::leanh::LeanObject,
    mut v_b_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4352_ = l_Lean_stateStackModify___redArg(v_ext_4349_, v_states_4350_, v_b_4351_);
    return v___x_4352_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(
    mut v_ext_4353_: *mut crate::leanh::LeanObject,
    mut v_b_4354_: *mut crate::leanh::LeanObject,
    mut v_s_4355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stateStack_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4361_: u8 = 0;
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4356_ = crate::leanh::lean_ctor_get(v_s_4355_, 0);
                v_scopedEntries_4357_ = crate::leanh::lean_ctor_get(v_s_4355_, 1);
                v_newEntries_4358_ = crate::leanh::lean_ctor_get(v_s_4355_, 2);
                v_isSharedCheck_4366_ = (!crate::leanh::lean_is_exclusive(v_s_4355_)) as u8;
                if v_isSharedCheck_4366_ == 0 {
                    v___x_4360_ = v_s_4355_;
                    v_isShared_4361_ = v_isSharedCheck_4366_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_newEntries_4358_);
                    crate::leanh::lean_inc(v_scopedEntries_4357_);
                    crate::leanh::lean_inc(v_stateStack_4356_);
                    crate::leanh::lean_dec(v_s_4355_);
                    v___x_4360_ = crate::leanh::lean_box(0);
                    v_isShared_4361_ = v_isSharedCheck_4366_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4362_ =
                    l_Lean_stateStackModify___redArg(v_ext_4353_, v_stateStack_4356_, v_b_4354_);
                if v_isShared_4361_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4360_, 0, v___x_4362_);
                    v___x_4364_ = v___x_4360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_scopedEntries_4357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 2, v_newEntries_4358_);
                    v___x_4364_ = v_reuseFailAlloc_4365_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addLocalEntry___redArg(
    mut v_ext_4367_: *mut crate::leanh::LeanObject,
    mut v_env_4368_: *mut crate::leanh::LeanObject,
    mut v_b_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ext_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ext_4370_ = crate::leanh::lean_ctor_get(v_ext_4367_, 1);
    crate::leanh::lean_inc_ref(v_ext_4370_);
    v___f_4371_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4371_, 0, v_ext_4367_);
    crate::leanh::lean_closure_set(v___f_4371_, 1, v_b_4369_);
    v___x_4372_ = crate::leanh::lean_box(1);
    v___x_4373_ = crate::leanh::lean_box(0);
    v___x_4374_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4370_,
        v_env_4368_,
        v___f_4371_,
        v___x_4372_,
        v___x_4373_,
    );
    return v___x_4374_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addLocalEntry(
    mut v_00_u03b1_4375_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4376_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4377_: *mut crate::leanh::LeanObject,
    mut v_ext_4378_: *mut crate::leanh::LeanObject,
    mut v_env_4379_: *mut crate::leanh::LeanObject,
    mut v_b_4380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4381_ =
        l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_4378_, v_env_4379_, v_b_4380_);
    return v___x_4381_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addCore___redArg(
    mut v_env_4382_: *mut crate::leanh::LeanObject,
    mut v_ext_4383_: *mut crate::leanh::LeanObject,
    mut v_b_4384_: *mut crate::leanh::LeanObject,
    mut v_kind_4385_: u8,
    mut v_namespaceName_4386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_kind_4385_ {
        0 => {
            let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_namespaceName_4386_);
            v___x_4387_ =
                l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_4383_, v_env_4382_, v_b_4384_);
            return v___x_4387_;
        }
        1 => {
            let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_namespaceName_4386_);
            v___x_4388_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(
                v_ext_4383_,
                v_env_4382_,
                v_b_4384_,
            );
            return v___x_4388_;
        }
        _ => {
            let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4389_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(
                v_ext_4383_,
                v_env_4382_,
                v_namespaceName_4386_,
                v_b_4384_,
            );
            return v___x_4389_;
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addCore___redArg___boxed(
    mut v_env_4390_: *mut crate::leanh::LeanObject,
    mut v_ext_4391_: *mut crate::leanh::LeanObject,
    mut v_b_4392_: *mut crate::leanh::LeanObject,
    mut v_kind_4393_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_4394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4395_: u8 = 0;
    let mut v_res_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4395_ = (crate::leanh::lean_unbox(v_kind_4393_) as u8);
    v_res_4396_ = l_Lean_ScopedEnvExtension_addCore___redArg(
        v_env_4390_,
        v_ext_4391_,
        v_b_4392_,
        v_kind_boxed_4395_,
        v_namespaceName_4394_,
    );
    return v_res_4396_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addCore(
    mut v_00_u03b1_4397_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4398_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4399_: *mut crate::leanh::LeanObject,
    mut v_env_4400_: *mut crate::leanh::LeanObject,
    mut v_ext_4401_: *mut crate::leanh::LeanObject,
    mut v_b_4402_: *mut crate::leanh::LeanObject,
    mut v_kind_4403_: u8,
    mut v_namespaceName_4404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4405_ = l_Lean_ScopedEnvExtension_addCore___redArg(
        v_env_4400_,
        v_ext_4401_,
        v_b_4402_,
        v_kind_4403_,
        v_namespaceName_4404_,
    );
    return v___x_4405_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addCore___boxed(
    mut v_00_u03b1_4406_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4407_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4408_: *mut crate::leanh::LeanObject,
    mut v_env_4409_: *mut crate::leanh::LeanObject,
    mut v_ext_4410_: *mut crate::leanh::LeanObject,
    mut v_b_4411_: *mut crate::leanh::LeanObject,
    mut v_kind_4412_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_4413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4414_: u8 = 0;
    let mut v_res_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4414_ = (crate::leanh::lean_unbox(v_kind_4412_) as u8);
    v_res_4415_ = l_Lean_ScopedEnvExtension_addCore(
        v_00_u03b1_4406_,
        v_00_u03b2_4407_,
        v_00_u03c3_4408_,
        v_env_4409_,
        v_ext_4410_,
        v_b_4411_,
        v_kind_boxed_4414_,
        v_namespaceName_4413_,
    );
    return v_res_4415_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___lam__0(
    mut v_ext_4416_: *mut crate::leanh::LeanObject,
    mut v_b_4417_: *mut crate::leanh::LeanObject,
    mut v_kind_4418_: u8,
    mut v_ns_4419_: *mut crate::leanh::LeanObject,
    mut v_x_4420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4421_ = l_Lean_ScopedEnvExtension_addCore___redArg(
        v_x_4420_,
        v_ext_4416_,
        v_b_4417_,
        v_kind_4418_,
        v_ns_4419_,
    );
    return v___x_4421_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(
    mut v_ext_4422_: *mut crate::leanh::LeanObject,
    mut v_b_4423_: *mut crate::leanh::LeanObject,
    mut v_kind_4424_: *mut crate::leanh::LeanObject,
    mut v_ns_4425_: *mut crate::leanh::LeanObject,
    mut v_x_4426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4427_: u8 = 0;
    let mut v_res_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4427_ = (crate::leanh::lean_unbox(v_kind_4424_) as u8);
    v_res_4428_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(
        v_ext_4422_,
        v_b_4423_,
        v_kind_boxed_4427_,
        v_ns_4425_,
        v_x_4426_,
    );
    return v_res_4428_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___lam__1(
    mut v_inst_4429_: *mut crate::leanh::LeanObject,
    mut v_ext_4430_: *mut crate::leanh::LeanObject,
    mut v_b_4431_: *mut crate::leanh::LeanObject,
    mut v_kind_4432_: u8,
    mut v_ns_4433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyEnv_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_4434_ = crate::leanh::lean_ctor_get(v_inst_4429_, 1);
    crate::leanh::lean_inc(v_modifyEnv_4434_);
    crate::leanh::lean_dec_ref(v_inst_4429_);
    v___x_4435_ = crate::leanh::lean_box((v_kind_4432_) as usize);
    v___f_4436_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4436_, 0, v_ext_4430_);
    crate::leanh::lean_closure_set(v___f_4436_, 1, v_b_4431_);
    crate::leanh::lean_closure_set(v___f_4436_, 2, v___x_4435_);
    crate::leanh::lean_closure_set(v___f_4436_, 3, v_ns_4433_);
    v___x_4437_ = crate::leanh::lean_apply_1(v_modifyEnv_4434_, v___f_4436_);
    return v___x_4437_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(
    mut v_inst_4438_: *mut crate::leanh::LeanObject,
    mut v_ext_4439_: *mut crate::leanh::LeanObject,
    mut v_b_4440_: *mut crate::leanh::LeanObject,
    mut v_kind_4441_: *mut crate::leanh::LeanObject,
    mut v_ns_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4443_: u8 = 0;
    let mut v_res_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4443_ = (crate::leanh::lean_unbox(v_kind_4441_) as u8);
    v_res_4444_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(
        v_inst_4438_,
        v_ext_4439_,
        v_b_4440_,
        v_kind_boxed_4443_,
        v_ns_4442_,
    );
    return v_res_4444_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg(
    mut v_inst_4445_: *mut crate::leanh::LeanObject,
    mut v_inst_4446_: *mut crate::leanh::LeanObject,
    mut v_inst_4447_: *mut crate::leanh::LeanObject,
    mut v_ext_4448_: *mut crate::leanh::LeanObject,
    mut v_b_4449_: *mut crate::leanh::LeanObject,
    mut v_kind_4450_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_4451_ = crate::leanh::lean_ctor_get(v_inst_4445_, 1);
    crate::leanh::lean_inc(v_toBind_4451_);
    crate::leanh::lean_dec_ref(v_inst_4445_);
    v_getCurrNamespace_4452_ = crate::leanh::lean_ctor_get(v_inst_4446_, 0);
    crate::leanh::lean_inc(v_getCurrNamespace_4452_);
    crate::leanh::lean_dec_ref(v_inst_4446_);
    v___x_4453_ = crate::leanh::lean_box((v_kind_4450_) as usize);
    v___f_4454_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4454_, 0, v_inst_4447_);
    crate::leanh::lean_closure_set(v___f_4454_, 1, v_ext_4448_);
    crate::leanh::lean_closure_set(v___f_4454_, 2, v_b_4449_);
    crate::leanh::lean_closure_set(v___f_4454_, 3, v___x_4453_);
    v___x_4455_ = crate::leanh::lean_apply_4(
        v_toBind_4451_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrNamespace_4452_,
        v___f_4454_,
    );
    return v___x_4455_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___boxed(
    mut v_inst_4456_: *mut crate::leanh::LeanObject,
    mut v_inst_4457_: *mut crate::leanh::LeanObject,
    mut v_inst_4458_: *mut crate::leanh::LeanObject,
    mut v_ext_4459_: *mut crate::leanh::LeanObject,
    mut v_b_4460_: *mut crate::leanh::LeanObject,
    mut v_kind_4461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4462_: u8 = 0;
    let mut v_res_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4462_ = (crate::leanh::lean_unbox(v_kind_4461_) as u8);
    v_res_4463_ = l_Lean_ScopedEnvExtension_add___redArg(
        v_inst_4456_,
        v_inst_4457_,
        v_inst_4458_,
        v_ext_4459_,
        v_b_4460_,
        v_kind_boxed_4462_,
    );
    return v_res_4463_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add(
    mut v_m_4464_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4465_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4466_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4467_: *mut crate::leanh::LeanObject,
    mut v_inst_4468_: *mut crate::leanh::LeanObject,
    mut v_inst_4469_: *mut crate::leanh::LeanObject,
    mut v_inst_4470_: *mut crate::leanh::LeanObject,
    mut v_ext_4471_: *mut crate::leanh::LeanObject,
    mut v_b_4472_: *mut crate::leanh::LeanObject,
    mut v_kind_4473_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Lean_ScopedEnvExtension_add___redArg(
        v_inst_4468_,
        v_inst_4469_,
        v_inst_4470_,
        v_ext_4471_,
        v_b_4472_,
        v_kind_4473_,
    );
    return v___x_4474_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___boxed(
    mut v_m_4475_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4476_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4477_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4478_: *mut crate::leanh::LeanObject,
    mut v_inst_4479_: *mut crate::leanh::LeanObject,
    mut v_inst_4480_: *mut crate::leanh::LeanObject,
    mut v_inst_4481_: *mut crate::leanh::LeanObject,
    mut v_ext_4482_: *mut crate::leanh::LeanObject,
    mut v_b_4483_: *mut crate::leanh::LeanObject,
    mut v_kind_4484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4485_: u8 = 0;
    let mut v_res_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4485_ = (crate::leanh::lean_unbox(v_kind_4484_) as u8);
    v_res_4486_ = l_Lean_ScopedEnvExtension_add(
        v_m_4475_,
        v_00_u03b1_4476_,
        v_00_u03b2_4477_,
        v_00_u03c3_4478_,
        v_inst_4479_,
        v_inst_4480_,
        v_inst_4481_,
        v_ext_4482_,
        v_b_4483_,
        v_kind_boxed_4485_,
    );
    return v_res_4486_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4490_ = l_Lean_ScopedEnvExtension_getState___redArg___closed__2;
    v___x_4491_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4492_ = crate::leanh::lean_unsigned_to_nat(209);
    v___x_4493_ = l_Lean_ScopedEnvExtension_getState___redArg___closed__1;
    v___x_4494_ = l_Lean_ScopedEnvExtension_getState___redArg___closed__0;
    v___x_4495_ = l_mkPanicMessageWithDecl(
        v___x_4494_,
        v___x_4493_,
        v___x_4492_,
        v___x_4491_,
        v___x_4490_,
    );
    return v___x_4495_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_getState___redArg(
    mut v_inst_4496_: *mut crate::leanh::LeanObject,
    mut v_ext_4497_: *mut crate::leanh::LeanObject,
    mut v_env_4498_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_4499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ext_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stateStack_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ext_4500_ = crate::leanh::lean_ctor_get(v_ext_4497_, 1);
    v___x_4501_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once),
        _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0,
    );
    v___x_4502_ = crate::leanh::lean_box(0);
    v___x_4503_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_4501_,
        v_ext_4500_,
        v_env_4498_,
        v_asyncMode_4499_,
        v___x_4502_,
    );
    v_stateStack_4504_ = crate::leanh::lean_ctor_get(v___x_4503_, 0);
    crate::leanh::lean_inc(v_stateStack_4504_);
    crate::leanh::lean_dec(v___x_4503_);
    if crate::leanh::lean_obj_tag(v_stateStack_4504_) == 1 {
        let mut v_head_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_state_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_4505_ = crate::leanh::lean_ctor_get(v_stateStack_4504_, 0);
        crate::leanh::lean_inc(v_head_4505_);
        crate::leanh::lean_dec_ref_known(v_stateStack_4504_, 2);
        v_state_4506_ = crate::leanh::lean_ctor_get(v_head_4505_, 0);
        crate::leanh::lean_inc(v_state_4506_);
        crate::leanh::lean_dec(v_head_4505_);
        return v_state_4506_;
    } else {
        let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stateStack_4504_);
        v___x_4507_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_getState___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once),
            _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3,
        );
        v___x_4508_ = l_panic___redArg(v_inst_4496_, v___x_4507_);
        return v___x_4508_;
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_getState___redArg___boxed(
    mut v_inst_4509_: *mut crate::leanh::LeanObject,
    mut v_ext_4510_: *mut crate::leanh::LeanObject,
    mut v_env_4511_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_4512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4513_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v_inst_4509_,
        v_ext_4510_,
        v_env_4511_,
        v_asyncMode_4512_,
    );
    crate::leanh::lean_dec(v_asyncMode_4512_);
    crate::leanh::lean_dec_ref(v_ext_4510_);
    crate::leanh::lean_dec(v_inst_4509_);
    return v_res_4513_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_getState(
    mut v_00_u03c3_4514_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4515_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4516_: *mut crate::leanh::LeanObject,
    mut v_inst_4517_: *mut crate::leanh::LeanObject,
    mut v_ext_4518_: *mut crate::leanh::LeanObject,
    mut v_env_4519_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_4520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v_inst_4517_,
        v_ext_4518_,
        v_env_4519_,
        v_asyncMode_4520_,
    );
    return v___x_4521_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_getState___boxed(
    mut v_00_u03c3_4522_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4523_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4524_: *mut crate::leanh::LeanObject,
    mut v_inst_4525_: *mut crate::leanh::LeanObject,
    mut v_ext_4526_: *mut crate::leanh::LeanObject,
    mut v_env_4527_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_4528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4529_ = l_Lean_ScopedEnvExtension_getState(
        v_00_u03c3_4522_,
        v_00_u03b1_4523_,
        v_00_u03b2_4524_,
        v_inst_4525_,
        v_ext_4526_,
        v_env_4527_,
        v_asyncMode_4528_,
    );
    crate::leanh::lean_dec(v_asyncMode_4528_);
    crate::leanh::lean_dec_ref(v_ext_4526_);
    crate::leanh::lean_dec(v_inst_4525_);
    return v_res_4529_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_ext_4530_: *mut crate::leanh::LeanObject,
    mut v_as_4531_: *mut crate::leanh::LeanObject,
    mut v_sz_4532_: usize,
    mut v_i_4533_: usize,
    mut v_b_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4535_: u8 = 0;
    let mut v_descr_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4540_: u8 = 0;
    let mut v_addEntry_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: usize = 0;
    let mut v___x_4548_: usize = 0;
    let mut v_reuseFailAlloc_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut v_unused_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4535_ = lean_usize_dec_lt(v_i_4533_, v_sz_4532_);
                if v___x_4535_ == 0 {
                    crate::leanh::lean_dec_ref(v_ext_4530_);
                    return v_b_4534_;
                } else {
                    v_descr_4536_ = crate::leanh::lean_ctor_get(v_ext_4530_, 0);
                    v_snd_4537_ = crate::leanh::lean_ctor_get(v_b_4534_, 1);
                    v_isSharedCheck_4551_ = (!crate::leanh::lean_is_exclusive(v_b_4534_)) as u8;
                    if v_isSharedCheck_4551_ == 0 {
                        v_unused_4552_ = crate::leanh::lean_ctor_get(v_b_4534_, 0);
                        crate::leanh::lean_dec(v_unused_4552_);
                        v___x_4539_ = v_b_4534_;
                        v_isShared_4540_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4537_);
                        crate::leanh::lean_dec(v_b_4534_);
                        v___x_4539_ = crate::leanh::lean_box(0);
                        v_isShared_4540_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4541_ = crate::leanh::lean_ctor_get(v_descr_4536_, 4);
                v___x_4542_ = crate::leanh::lean_box(0);
                v_a_4543_ = lean_array_uget_borrowed(v_as_4531_, v_i_4533_);
                crate::leanh::lean_inc(v_addEntry_4541_);
                crate::leanh::lean_inc(v_a_4543_);
                v_state_4544_ =
                    crate::leanh::lean_apply_2(v_addEntry_4541_, v_snd_4537_, v_a_4543_);
                if v_isShared_4540_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4539_, 1, v_state_4544_);
                    crate::leanh::lean_ctor_set(v___x_4539_, 0, v___x_4542_);
                    v___x_4546_ = v___x_4539_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_state_4544_);
                    v___x_4546_ = v_reuseFailAlloc_4550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4547_ = 1usize;
                v___x_4548_ = lean_usize_add(v_i_4533_, v___x_4547_);
                v_i_4533_ = v___x_4548_;
                v_b_4534_ = v___x_4546_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(
    mut v_ext_4553_: *mut crate::leanh::LeanObject,
    mut v_as_4554_: *mut crate::leanh::LeanObject,
    mut v_sz_4555_: *mut crate::leanh::LeanObject,
    mut v_i_4556_: *mut crate::leanh::LeanObject,
    mut v_b_4557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4558_: usize = 0;
    let mut v_i_boxed_4559_: usize = 0;
    let mut v_res_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4558_ = crate::leanh::lean_unbox_usize(v_sz_4555_);
    crate::leanh::lean_dec(v_sz_4555_);
    v_i_boxed_4559_ = crate::leanh::lean_unbox_usize(v_i_4556_);
    crate::leanh::lean_dec(v_i_4556_);
    v_res_4560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_4553_, v_as_4554_, v_sz_boxed_4558_, v_i_boxed_4559_, v_b_4557_);
    crate::leanh::lean_dec_ref(v_as_4554_);
    return v_res_4560_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(
    mut v_ext_4561_: *mut crate::leanh::LeanObject,
    mut v_as_4562_: *mut crate::leanh::LeanObject,
    mut v_sz_4563_: usize,
    mut v_i_4564_: usize,
    mut v_b_4565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4566_: u8 = 0;
    let mut v_descr_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4571_: u8 = 0;
    let mut v_addEntry_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: usize = 0;
    let mut v___x_4579_: usize = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4582_: u8 = 0;
    let mut v_unused_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4566_ = lean_usize_dec_lt(v_i_4564_, v_sz_4563_);
                if v___x_4566_ == 0 {
                    crate::leanh::lean_dec_ref(v_ext_4561_);
                    return v_b_4565_;
                } else {
                    v_descr_4567_ = crate::leanh::lean_ctor_get(v_ext_4561_, 0);
                    v_snd_4568_ = crate::leanh::lean_ctor_get(v_b_4565_, 1);
                    v_isSharedCheck_4582_ = (!crate::leanh::lean_is_exclusive(v_b_4565_)) as u8;
                    if v_isSharedCheck_4582_ == 0 {
                        v_unused_4583_ = crate::leanh::lean_ctor_get(v_b_4565_, 0);
                        crate::leanh::lean_dec(v_unused_4583_);
                        v___x_4570_ = v_b_4565_;
                        v_isShared_4571_ = v_isSharedCheck_4582_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4568_);
                        crate::leanh::lean_dec(v_b_4565_);
                        v___x_4570_ = crate::leanh::lean_box(0);
                        v_isShared_4571_ = v_isSharedCheck_4582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4572_ = crate::leanh::lean_ctor_get(v_descr_4567_, 4);
                v___x_4573_ = crate::leanh::lean_box(0);
                v_a_4574_ = lean_array_uget_borrowed(v_as_4562_, v_i_4564_);
                crate::leanh::lean_inc(v_addEntry_4572_);
                crate::leanh::lean_inc(v_a_4574_);
                v_state_4575_ =
                    crate::leanh::lean_apply_2(v_addEntry_4572_, v_snd_4568_, v_a_4574_);
                if v_isShared_4571_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4570_, 1, v_state_4575_);
                    crate::leanh::lean_ctor_set(v___x_4570_, 0, v___x_4573_);
                    v___x_4577_ = v___x_4570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4581_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4581_, 1, v_state_4575_);
                    v___x_4577_ = v_reuseFailAlloc_4581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4578_ = 1usize;
                v___x_4579_ = lean_usize_add(v_i_4564_, v___x_4578_);
                v___x_4580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_4561_, v_as_4562_, v_sz_4563_, v___x_4579_, v___x_4577_);
                return v___x_4580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ext_4584_: *mut crate::leanh::LeanObject,
    mut v_as_4585_: *mut crate::leanh::LeanObject,
    mut v_sz_4586_: *mut crate::leanh::LeanObject,
    mut v_i_4587_: *mut crate::leanh::LeanObject,
    mut v_b_4588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4589_: usize = 0;
    let mut v_i_boxed_4590_: usize = 0;
    let mut v_res_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4589_ = crate::leanh::lean_unbox_usize(v_sz_4586_);
    crate::leanh::lean_dec(v_sz_4586_);
    v_i_boxed_4590_ = crate::leanh::lean_unbox_usize(v_i_4587_);
    crate::leanh::lean_dec(v_i_4587_);
    v_res_4591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_4584_, v_as_4585_, v_sz_boxed_4589_, v_i_boxed_4590_, v_b_4588_);
    crate::leanh::lean_dec_ref(v_as_4585_);
    return v_res_4591_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(
    mut v_init_4592_: *mut crate::leanh::LeanObject,
    mut v_ext_4593_: *mut crate::leanh::LeanObject,
    mut v_n_4594_: *mut crate::leanh::LeanObject,
    mut v_b_4595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_n_4594_) == 0 {
        let mut v_cs_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4599_: usize = 0;
        let mut v___x_4600_: usize = 0;
        let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_cs_4596_ = crate::leanh::lean_ctor_get(v_n_4594_, 0);
        v___x_4597_ = crate::leanh::lean_box(0);
        v___x_4598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4598_, 0, v___x_4597_);
        crate::leanh::lean_ctor_set(v___x_4598_, 1, v_b_4595_);
        v_sz_4599_ = lean_array_size(v_cs_4596_);
        v___x_4600_ = 0usize;
        v___x_4601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_4592_, v_ext_4593_, v_cs_4596_, v_sz_4599_, v___x_4600_, v___x_4598_);
        v_fst_4602_ = crate::leanh::lean_ctor_get(v___x_4601_, 0);
        crate::leanh::lean_inc(v_fst_4602_);
        if crate::leanh::lean_obj_tag(v_fst_4602_) == 0 {
            let mut v_snd_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_snd_4603_ = crate::leanh::lean_ctor_get(v___x_4601_, 1);
            crate::leanh::lean_inc(v_snd_4603_);
            crate::leanh::lean_dec_ref(v___x_4601_);
            v___x_4604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4604_, 0, v_snd_4603_);
            return v___x_4604_;
        } else {
            let mut v_val_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_4601_);
            v_val_4605_ = crate::leanh::lean_ctor_get(v_fst_4602_, 0);
            crate::leanh::lean_inc(v_val_4605_);
            crate::leanh::lean_dec_ref_known(v_fst_4602_, 1);
            return v_val_4605_;
        }
    } else {
        let mut v_vs_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4609_: usize = 0;
        let mut v___x_4610_: usize = 0;
        let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_vs_4606_ = crate::leanh::lean_ctor_get(v_n_4594_, 0);
        v___x_4607_ = crate::leanh::lean_box(0);
        v___x_4608_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4608_, 0, v___x_4607_);
        crate::leanh::lean_ctor_set(v___x_4608_, 1, v_b_4595_);
        v_sz_4609_ = lean_array_size(v_vs_4606_);
        v___x_4610_ = 0usize;
        v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_4593_, v_vs_4606_, v_sz_4609_, v___x_4610_, v___x_4608_);
        v_fst_4612_ = crate::leanh::lean_ctor_get(v___x_4611_, 0);
        crate::leanh::lean_inc(v_fst_4612_);
        if crate::leanh::lean_obj_tag(v_fst_4612_) == 0 {
            let mut v_snd_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_snd_4613_ = crate::leanh::lean_ctor_get(v___x_4611_, 1);
            crate::leanh::lean_inc(v_snd_4613_);
            crate::leanh::lean_dec_ref(v___x_4611_);
            v___x_4614_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4614_, 0, v_snd_4613_);
            return v___x_4614_;
        } else {
            let mut v_val_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_4611_);
            v_val_4615_ = crate::leanh::lean_ctor_get(v_fst_4612_, 0);
            crate::leanh::lean_inc(v_val_4615_);
            crate::leanh::lean_dec_ref_known(v_fst_4612_, 1);
            return v_val_4615_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(
    mut v_init_4616_: *mut crate::leanh::LeanObject,
    mut v_ext_4617_: *mut crate::leanh::LeanObject,
    mut v_as_4618_: *mut crate::leanh::LeanObject,
    mut v_sz_4619_: usize,
    mut v_i_4620_: usize,
    mut v_b_4621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4622_: u8 = 0;
    let mut v_snd_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v_a_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: usize = 0;
    let mut v___x_4638_: usize = 0;
    let mut v_reuseFailAlloc_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4641_: u8 = 0;
    let mut v_unused_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4622_ = lean_usize_dec_lt(v_i_4620_, v_sz_4619_);
                if v___x_4622_ == 0 {
                    crate::leanh::lean_dec_ref(v_ext_4617_);
                    return v_b_4621_;
                } else {
                    v_snd_4623_ = crate::leanh::lean_ctor_get(v_b_4621_, 1);
                    v_isSharedCheck_4641_ = (!crate::leanh::lean_is_exclusive(v_b_4621_)) as u8;
                    if v_isSharedCheck_4641_ == 0 {
                        v_unused_4642_ = crate::leanh::lean_ctor_get(v_b_4621_, 0);
                        crate::leanh::lean_dec(v_unused_4642_);
                        v___x_4625_ = v_b_4621_;
                        v_isShared_4626_ = v_isSharedCheck_4641_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4623_);
                        crate::leanh::lean_dec(v_b_4621_);
                        v___x_4625_ = crate::leanh::lean_box(0);
                        v_isShared_4626_ = v_isSharedCheck_4641_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4627_ = lean_array_uget_borrowed(v_as_4618_, v_i_4620_);
                crate::leanh::lean_inc(v_snd_4623_);
                crate::leanh::lean_inc_ref(v_ext_4617_);
                v___x_4628_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_4616_, v_ext_4617_, v_a_4627_, v_snd_4623_);
                if crate::leanh::lean_obj_tag(v___x_4628_) == 0 {
                    crate::leanh::lean_dec_ref(v_ext_4617_);
                    v___x_4629_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4629_, 0, v___x_4628_);
                    if v_isShared_4626_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4625_, 0, v___x_4629_);
                        v___x_4631_ = v___x_4625_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4629_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4632_, 1, v_snd_4623_);
                        v___x_4631_ = v_reuseFailAlloc_4632_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_4623_);
                    v_a_4633_ = crate::leanh::lean_ctor_get(v___x_4628_, 0);
                    crate::leanh::lean_inc(v_a_4633_);
                    crate::leanh::lean_dec_ref_known(v___x_4628_, 1);
                    v___x_4634_ = crate::leanh::lean_box(0);
                    if v_isShared_4626_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4625_, 1, v_a_4633_);
                        crate::leanh::lean_ctor_set(v___x_4625_, 0, v___x_4634_);
                        v___x_4636_ = v___x_4625_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4640_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4634_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 1, v_a_4633_);
                        v___x_4636_ = v_reuseFailAlloc_4640_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4631_;
            }
            3 => {
                v___x_4637_ = 1usize;
                v___x_4638_ = lean_usize_add(v_i_4620_, v___x_4637_);
                v_i_4620_ = v___x_4638_;
                v_b_4621_ = v___x_4636_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_init_4643_: *mut crate::leanh::LeanObject,
    mut v_ext_4644_: *mut crate::leanh::LeanObject,
    mut v_as_4645_: *mut crate::leanh::LeanObject,
    mut v_sz_4646_: *mut crate::leanh::LeanObject,
    mut v_i_4647_: *mut crate::leanh::LeanObject,
    mut v_b_4648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4649_: usize = 0;
    let mut v_i_boxed_4650_: usize = 0;
    let mut v_res_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4649_ = crate::leanh::lean_unbox_usize(v_sz_4646_);
    crate::leanh::lean_dec(v_sz_4646_);
    v_i_boxed_4650_ = crate::leanh::lean_unbox_usize(v_i_4647_);
    crate::leanh::lean_dec(v_i_4647_);
    v_res_4651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_4643_, v_ext_4644_, v_as_4645_, v_sz_boxed_4649_, v_i_boxed_4650_, v_b_4648_);
    crate::leanh::lean_dec_ref(v_as_4645_);
    crate::leanh::lean_dec(v_init_4643_);
    return v_res_4651_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(
    mut v_init_4652_: *mut crate::leanh::LeanObject,
    mut v_ext_4653_: *mut crate::leanh::LeanObject,
    mut v_n_4654_: *mut crate::leanh::LeanObject,
    mut v_b_4655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4656_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_4652_, v_ext_4653_, v_n_4654_, v_b_4655_);
    crate::leanh::lean_dec_ref(v_n_4654_);
    crate::leanh::lean_dec(v_init_4652_);
    return v_res_4656_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(
    mut v_ext_4657_: *mut crate::leanh::LeanObject,
    mut v_as_4658_: *mut crate::leanh::LeanObject,
    mut v_sz_4659_: usize,
    mut v_i_4660_: usize,
    mut v_b_4661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4662_: u8 = 0;
    let mut v_descr_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4667_: u8 = 0;
    let mut v_addEntry_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: usize = 0;
    let mut v___x_4675_: usize = 0;
    let mut v_reuseFailAlloc_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4678_: u8 = 0;
    let mut v_unused_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4662_ = lean_usize_dec_lt(v_i_4660_, v_sz_4659_);
                if v___x_4662_ == 0 {
                    crate::leanh::lean_dec_ref(v_ext_4657_);
                    return v_b_4661_;
                } else {
                    v_descr_4663_ = crate::leanh::lean_ctor_get(v_ext_4657_, 0);
                    v_snd_4664_ = crate::leanh::lean_ctor_get(v_b_4661_, 1);
                    v_isSharedCheck_4678_ = (!crate::leanh::lean_is_exclusive(v_b_4661_)) as u8;
                    if v_isSharedCheck_4678_ == 0 {
                        v_unused_4679_ = crate::leanh::lean_ctor_get(v_b_4661_, 0);
                        crate::leanh::lean_dec(v_unused_4679_);
                        v___x_4666_ = v_b_4661_;
                        v_isShared_4667_ = v_isSharedCheck_4678_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4664_);
                        crate::leanh::lean_dec(v_b_4661_);
                        v___x_4666_ = crate::leanh::lean_box(0);
                        v_isShared_4667_ = v_isSharedCheck_4678_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4668_ = crate::leanh::lean_ctor_get(v_descr_4663_, 4);
                v___x_4669_ = crate::leanh::lean_box(0);
                v_a_4670_ = lean_array_uget_borrowed(v_as_4658_, v_i_4660_);
                crate::leanh::lean_inc(v_addEntry_4668_);
                crate::leanh::lean_inc(v_a_4670_);
                v_state_4671_ =
                    crate::leanh::lean_apply_2(v_addEntry_4668_, v_snd_4664_, v_a_4670_);
                if v_isShared_4667_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4666_, 1, v_state_4671_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 0, v___x_4669_);
                    v___x_4673_ = v___x_4666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4677_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_state_4671_);
                    v___x_4673_ = v_reuseFailAlloc_4677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4674_ = 1usize;
                v___x_4675_ = lean_usize_add(v_i_4660_, v___x_4674_);
                v_i_4660_ = v___x_4675_;
                v_b_4661_ = v___x_4673_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ext_4680_: *mut crate::leanh::LeanObject,
    mut v_as_4681_: *mut crate::leanh::LeanObject,
    mut v_sz_4682_: *mut crate::leanh::LeanObject,
    mut v_i_4683_: *mut crate::leanh::LeanObject,
    mut v_b_4684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4685_: usize = 0;
    let mut v_i_boxed_4686_: usize = 0;
    let mut v_res_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4685_ = crate::leanh::lean_unbox_usize(v_sz_4682_);
    crate::leanh::lean_dec(v_sz_4682_);
    v_i_boxed_4686_ = crate::leanh::lean_unbox_usize(v_i_4683_);
    crate::leanh::lean_dec(v_i_4683_);
    v_res_4687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_4680_, v_as_4681_, v_sz_boxed_4685_, v_i_boxed_4686_, v_b_4684_);
    crate::leanh::lean_dec_ref(v_as_4681_);
    return v_res_4687_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(
    mut v_ext_4688_: *mut crate::leanh::LeanObject,
    mut v_as_4689_: *mut crate::leanh::LeanObject,
    mut v_sz_4690_: usize,
    mut v_i_4691_: usize,
    mut v_b_4692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4693_: u8 = 0;
    let mut v_descr_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4698_: u8 = 0;
    let mut v_addEntry_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: usize = 0;
    let mut v___x_4706_: usize = 0;
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4709_: u8 = 0;
    let mut v_unused_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4693_ = lean_usize_dec_lt(v_i_4691_, v_sz_4690_);
                if v___x_4693_ == 0 {
                    crate::leanh::lean_dec_ref(v_ext_4688_);
                    return v_b_4692_;
                } else {
                    v_descr_4694_ = crate::leanh::lean_ctor_get(v_ext_4688_, 0);
                    v_snd_4695_ = crate::leanh::lean_ctor_get(v_b_4692_, 1);
                    v_isSharedCheck_4709_ = (!crate::leanh::lean_is_exclusive(v_b_4692_)) as u8;
                    if v_isSharedCheck_4709_ == 0 {
                        v_unused_4710_ = crate::leanh::lean_ctor_get(v_b_4692_, 0);
                        crate::leanh::lean_dec(v_unused_4710_);
                        v___x_4697_ = v_b_4692_;
                        v_isShared_4698_ = v_isSharedCheck_4709_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4695_);
                        crate::leanh::lean_dec(v_b_4692_);
                        v___x_4697_ = crate::leanh::lean_box(0);
                        v_isShared_4698_ = v_isSharedCheck_4709_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4699_ = crate::leanh::lean_ctor_get(v_descr_4694_, 4);
                v___x_4700_ = crate::leanh::lean_box(0);
                v_a_4701_ = lean_array_uget_borrowed(v_as_4689_, v_i_4691_);
                crate::leanh::lean_inc(v_addEntry_4699_);
                crate::leanh::lean_inc(v_a_4701_);
                v_state_4702_ =
                    crate::leanh::lean_apply_2(v_addEntry_4699_, v_snd_4695_, v_a_4701_);
                if v_isShared_4698_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4697_, 1, v_state_4702_);
                    crate::leanh::lean_ctor_set(v___x_4697_, 0, v___x_4700_);
                    v___x_4704_ = v___x_4697_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4708_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_state_4702_);
                    v___x_4704_ = v_reuseFailAlloc_4708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4705_ = 1usize;
                v___x_4706_ = lean_usize_add(v_i_4691_, v___x_4705_);
                v___x_4707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_4688_, v_as_4689_, v_sz_4690_, v___x_4706_, v___x_4704_);
                return v___x_4707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(
    mut v_ext_4711_: *mut crate::leanh::LeanObject,
    mut v_as_4712_: *mut crate::leanh::LeanObject,
    mut v_sz_4713_: *mut crate::leanh::LeanObject,
    mut v_i_4714_: *mut crate::leanh::LeanObject,
    mut v_b_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4716_: usize = 0;
    let mut v_i_boxed_4717_: usize = 0;
    let mut v_res_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4716_ = crate::leanh::lean_unbox_usize(v_sz_4713_);
    crate::leanh::lean_dec(v_sz_4713_);
    v_i_boxed_4717_ = crate::leanh::lean_unbox_usize(v_i_4714_);
    crate::leanh::lean_dec(v_i_4714_);
    v_res_4718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_4711_, v_as_4712_, v_sz_boxed_4716_, v_i_boxed_4717_, v_b_4715_);
    crate::leanh::lean_dec_ref(v_as_4712_);
    return v_res_4718_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(
    mut v_ext_4719_: *mut crate::leanh::LeanObject,
    mut v_t_4720_: *mut crate::leanh::LeanObject,
    mut v_init_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_root_4722_ = crate::leanh::lean_ctor_get(v_t_4720_, 0);
    v_tail_4723_ = crate::leanh::lean_ctor_get(v_t_4720_, 1);
    crate::leanh::lean_inc_ref(v_ext_4719_);
    crate::leanh::lean_inc(v_init_4721_);
    v___x_4724_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_4721_, v_ext_4719_, v_root_4722_, v_init_4721_);
    crate::leanh::lean_dec(v_init_4721_);
    if crate::leanh::lean_obj_tag(v___x_4724_) == 0 {
        let mut v_a_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_ext_4719_);
        v_a_4725_ = crate::leanh::lean_ctor_get(v___x_4724_, 0);
        crate::leanh::lean_inc(v_a_4725_);
        crate::leanh::lean_dec_ref_known(v___x_4724_, 1);
        return v_a_4725_;
    } else {
        let mut v_a_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4729_: usize = 0;
        let mut v___x_4730_: usize = 0;
        let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4726_ = crate::leanh::lean_ctor_get(v___x_4724_, 0);
        crate::leanh::lean_inc(v_a_4726_);
        crate::leanh::lean_dec_ref_known(v___x_4724_, 1);
        v___x_4727_ = crate::leanh::lean_box(0);
        v___x_4728_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4728_, 0, v___x_4727_);
        crate::leanh::lean_ctor_set(v___x_4728_, 1, v_a_4726_);
        v_sz_4729_ = lean_array_size(v_tail_4723_);
        v___x_4730_ = 0usize;
        v___x_4731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_4719_, v_tail_4723_, v_sz_4729_, v___x_4730_, v___x_4728_);
        v_fst_4732_ = crate::leanh::lean_ctor_get(v___x_4731_, 0);
        crate::leanh::lean_inc(v_fst_4732_);
        if crate::leanh::lean_obj_tag(v_fst_4732_) == 0 {
            let mut v_snd_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_snd_4733_ = crate::leanh::lean_ctor_get(v___x_4731_, 1);
            crate::leanh::lean_inc(v_snd_4733_);
            crate::leanh::lean_dec_ref(v___x_4731_);
            return v_snd_4733_;
        } else {
            let mut v_val_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_4731_);
            v_val_4734_ = crate::leanh::lean_ctor_get(v_fst_4732_, 0);
            crate::leanh::lean_inc(v_val_4734_);
            crate::leanh::lean_dec_ref_known(v_fst_4732_, 1);
            return v_val_4734_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(
    mut v_ext_4735_: *mut crate::leanh::LeanObject,
    mut v_t_4736_: *mut crate::leanh::LeanObject,
    mut v_init_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4738_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_4735_, v_t_4736_, v_init_4737_);
    crate::leanh::lean_dec_ref(v_t_4736_);
    return v_res_4738_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(
    mut v_namespaceName_4739_: *mut crate::leanh::LeanObject,
    mut v_ext_4740_: *mut crate::leanh::LeanObject,
    mut v_s_4741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stateStack_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4749_: u8 = 0;
    let mut v___y_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_state_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_4758_: u8 = 0;
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4762_: u8 = 0;
    let mut v_activeScopes_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: u8 = 0;
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut v_isSharedCheck_4775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4742_ = crate::leanh::lean_ctor_get(v_s_4741_, 0);
                crate::leanh::lean_inc(v_stateStack_4742_);
                if crate::leanh::lean_obj_tag(v_stateStack_4742_) == 1 {
                    v_scopedEntries_4743_ = crate::leanh::lean_ctor_get(v_s_4741_, 1);
                    v_newEntries_4744_ = crate::leanh::lean_ctor_get(v_s_4741_, 2);
                    v_head_4745_ = crate::leanh::lean_ctor_get(v_stateStack_4742_, 0);
                    v_tail_4746_ = crate::leanh::lean_ctor_get(v_stateStack_4742_, 1);
                    v_isSharedCheck_4775_ =
                        (!crate::leanh::lean_is_exclusive(v_stateStack_4742_)) as u8;
                    if v_isSharedCheck_4775_ == 0 {
                        v___x_4748_ = v_stateStack_4742_;
                        v_isShared_4749_ = v_isSharedCheck_4775_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4746_);
                        crate::leanh::lean_inc(v_head_4745_);
                        crate::leanh::lean_dec(v_stateStack_4742_);
                        v___x_4748_ = crate::leanh::lean_box(0);
                        v_isShared_4749_ = v_isSharedCheck_4775_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stateStack_4742_);
                    crate::leanh::lean_dec_ref(v_ext_4740_);
                    crate::leanh::lean_dec(v_namespaceName_4739_);
                    return v_s_4741_;
                }
            }
            1 => {
                v_state_4756_ = crate::leanh::lean_ctor_get(v_head_4745_, 0);
                v_activeScopes_4757_ = crate::leanh::lean_ctor_get(v_head_4745_, 1);
                v_delimitsLocal_4758_ = crate::leanh::lean_ctor_get_uint8(
                    v_head_4745_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_4774_ = (!crate::leanh::lean_is_exclusive(v_head_4745_)) as u8;
                if v_isSharedCheck_4774_ == 0 {
                    v___x_4760_ = v_head_4745_;
                    v_isShared_4761_ = v_isSharedCheck_4774_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeScopes_4757_);
                    crate::leanh::lean_inc(v_state_4756_);
                    crate::leanh::lean_dec(v_head_4745_);
                    v___x_4760_ = crate::leanh::lean_box(0);
                    v_isShared_4761_ = v_isSharedCheck_4774_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_4749_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4748_, 0, v___y_4751_);
                    v___x_4753_ = v___x_4748_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4755_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___y_4751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4755_, 1, v_tail_4746_);
                    v___x_4753_ = v_reuseFailAlloc_4755_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4754_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4754_, 0, v___x_4753_);
                crate::leanh::lean_ctor_set(v___x_4754_, 1, v_scopedEntries_4743_);
                crate::leanh::lean_ctor_set(v___x_4754_, 2, v_newEntries_4744_);
                return v___x_4754_;
            }
            4 => {
                v___x_4762_ = l_Lean_NameSet_contains(v_activeScopes_4757_, v_namespaceName_4739_);
                if v___x_4762_ == 0 {
                    crate::leanh::lean_inc(v_newEntries_4744_);
                    crate::leanh::lean_inc_ref(v_scopedEntries_4743_);
                    crate::leanh::lean_dec_ref(v_s_4741_);
                    crate::leanh::lean_inc(v_namespaceName_4739_);
                    v_activeScopes_4763_ =
                        l_Lean_NameSet_insert(v_activeScopes_4757_, v_namespaceName_4739_);
                    v___x_4764_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_4743_, v_namespaceName_4739_);
                    crate::leanh::lean_dec(v_namespaceName_4739_);
                    if crate::leanh::lean_obj_tag(v___x_4764_) == 0 {
                        crate::leanh::lean_dec_ref(v_ext_4740_);
                        if v_isShared_4761_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4760_, 1, v_activeScopes_4763_);
                            v___x_4766_ = v___x_4760_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4767_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_state_4756_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4767_,
                                1,
                                v_activeScopes_4763_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_4767_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v_delimitsLocal_4758_,
                            );
                            v___x_4766_ = v_reuseFailAlloc_4767_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_val_4768_ = crate::leanh::lean_ctor_get(v___x_4764_, 0);
                        crate::leanh::lean_inc(v_val_4768_);
                        crate::leanh::lean_dec_ref_known(v___x_4764_, 1);
                        v___x_4769_ = 1;
                        v___x_4770_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_4740_, v_val_4768_, v_state_4756_);
                        crate::leanh::lean_dec(v_val_4768_);
                        if v_isShared_4761_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4760_, 1, v_activeScopes_4763_);
                            crate::leanh::lean_ctor_set(v___x_4760_, 0, v___x_4770_);
                            v___x_4772_ = v___x_4760_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4773_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4770_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4773_,
                                1,
                                v_activeScopes_4763_,
                            );
                            v___x_4772_ = v_reuseFailAlloc_4773_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4760_);
                    crate::leanh::lean_dec(v_activeScopes_4757_);
                    crate::leanh::lean_dec(v_state_4756_);
                    crate::leanh::lean_del_object(v___x_4748_);
                    crate::leanh::lean_dec(v_tail_4746_);
                    crate::leanh::lean_dec_ref(v_ext_4740_);
                    crate::leanh::lean_dec(v_namespaceName_4739_);
                    return v_s_4741_;
                }
            }
            5 => {
                v___y_4751_ = v___x_4766_;
                state = 2;
                continue;
            }
            6 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4769_,
                );
                v___y_4751_ = v___x_4772_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_activateScoped___redArg(
    mut v_ext_4776_: *mut crate::leanh::LeanObject,
    mut v_env_4777_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_4778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ext_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ext_4779_ = crate::leanh::lean_ctor_get(v_ext_4776_, 1);
    crate::leanh::lean_inc_ref(v_ext_4779_);
    v___f_4780_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4780_, 0, v_namespaceName_4778_);
    crate::leanh::lean_closure_set(v___f_4780_, 1, v_ext_4776_);
    v___x_4781_ = crate::leanh::lean_box(1);
    v___x_4782_ = crate::leanh::lean_box(0);
    v___x_4783_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4779_,
        v_env_4777_,
        v___f_4780_,
        v___x_4781_,
        v___x_4782_,
    );
    return v___x_4783_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_activateScoped(
    mut v_00_u03b1_4784_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4785_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4786_: *mut crate::leanh::LeanObject,
    mut v_ext_4787_: *mut crate::leanh::LeanObject,
    mut v_env_4788_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_4789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4790_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(
        v_ext_4787_,
        v_env_4788_,
        v_namespaceName_4789_,
    );
    return v___x_4790_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(
    mut v_00_u03b2_4791_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4792_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4793_: *mut crate::leanh::LeanObject,
    mut v_ext_4794_: *mut crate::leanh::LeanObject,
    mut v_t_4795_: *mut crate::leanh::LeanObject,
    mut v_init_4796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4797_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_4794_, v_t_4795_, v_init_4796_);
    return v___x_4797_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(
    mut v_00_u03b2_4798_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4799_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4800_: *mut crate::leanh::LeanObject,
    mut v_ext_4801_: *mut crate::leanh::LeanObject,
    mut v_t_4802_: *mut crate::leanh::LeanObject,
    mut v_init_4803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4804_ =
        l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(
            v_00_u03b2_4798_,
            v_00_u03c3_4799_,
            v_00_u03b1_4800_,
            v_ext_4801_,
            v_t_4802_,
            v_init_4803_,
        );
    crate::leanh::lean_dec_ref(v_t_4802_);
    return v_res_4804_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(
    mut v_00_u03b2_4805_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4806_: *mut crate::leanh::LeanObject,
    mut v_init_4807_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4808_: *mut crate::leanh::LeanObject,
    mut v_ext_4809_: *mut crate::leanh::LeanObject,
    mut v_n_4810_: *mut crate::leanh::LeanObject,
    mut v_b_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4812_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_4807_, v_ext_4809_, v_n_4810_, v_b_4811_);
    return v___x_4812_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(
    mut v_00_u03b2_4813_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4814_: *mut crate::leanh::LeanObject,
    mut v_init_4815_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4816_: *mut crate::leanh::LeanObject,
    mut v_ext_4817_: *mut crate::leanh::LeanObject,
    mut v_n_4818_: *mut crate::leanh::LeanObject,
    mut v_b_4819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4820_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_4813_, v_00_u03c3_4814_, v_init_4815_, v_00_u03b1_4816_, v_ext_4817_, v_n_4818_, v_b_4819_);
    crate::leanh::lean_dec_ref(v_n_4818_);
    crate::leanh::lean_dec(v_init_4815_);
    return v_res_4820_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(
    mut v_00_u03b2_4821_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4822_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4823_: *mut crate::leanh::LeanObject,
    mut v_ext_4824_: *mut crate::leanh::LeanObject,
    mut v_as_4825_: *mut crate::leanh::LeanObject,
    mut v_sz_4826_: usize,
    mut v_i_4827_: usize,
    mut v_b_4828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_4824_, v_as_4825_, v_sz_4826_, v_i_4827_, v_b_4828_);
    return v___x_4829_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(
    mut v_00_u03b2_4830_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4831_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4832_: *mut crate::leanh::LeanObject,
    mut v_ext_4833_: *mut crate::leanh::LeanObject,
    mut v_as_4834_: *mut crate::leanh::LeanObject,
    mut v_sz_4835_: *mut crate::leanh::LeanObject,
    mut v_i_4836_: *mut crate::leanh::LeanObject,
    mut v_b_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4838_: usize = 0;
    let mut v_i_boxed_4839_: usize = 0;
    let mut v_res_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4838_ = crate::leanh::lean_unbox_usize(v_sz_4835_);
    crate::leanh::lean_dec(v_sz_4835_);
    v_i_boxed_4839_ = crate::leanh::lean_unbox_usize(v_i_4836_);
    crate::leanh::lean_dec(v_i_4836_);
    v_res_4840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_4830_, v_00_u03c3_4831_, v_00_u03b1_4832_, v_ext_4833_, v_as_4834_, v_sz_boxed_4838_, v_i_boxed_4839_, v_b_4837_);
    crate::leanh::lean_dec_ref(v_as_4834_);
    return v_res_4840_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4841_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4842_: *mut crate::leanh::LeanObject,
    mut v_init_4843_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4844_: *mut crate::leanh::LeanObject,
    mut v_ext_4845_: *mut crate::leanh::LeanObject,
    mut v_as_4846_: *mut crate::leanh::LeanObject,
    mut v_sz_4847_: usize,
    mut v_i_4848_: usize,
    mut v_b_4849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_4843_, v_ext_4845_, v_as_4846_, v_sz_4847_, v_i_4848_, v_b_4849_);
    return v___x_4850_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4851_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4852_: *mut crate::leanh::LeanObject,
    mut v_init_4853_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4854_: *mut crate::leanh::LeanObject,
    mut v_ext_4855_: *mut crate::leanh::LeanObject,
    mut v_as_4856_: *mut crate::leanh::LeanObject,
    mut v_sz_4857_: *mut crate::leanh::LeanObject,
    mut v_i_4858_: *mut crate::leanh::LeanObject,
    mut v_b_4859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4860_: usize = 0;
    let mut v_i_boxed_4861_: usize = 0;
    let mut v_res_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4860_ = crate::leanh::lean_unbox_usize(v_sz_4857_);
    crate::leanh::lean_dec(v_sz_4857_);
    v_i_boxed_4861_ = crate::leanh::lean_unbox_usize(v_i_4858_);
    crate::leanh::lean_dec(v_i_4858_);
    v_res_4862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_4851_, v_00_u03c3_4852_, v_init_4853_, v_00_u03b1_4854_, v_ext_4855_, v_as_4856_, v_sz_boxed_4860_, v_i_boxed_4861_, v_b_4859_);
    crate::leanh::lean_dec_ref(v_as_4856_);
    crate::leanh::lean_dec(v_init_4853_);
    return v_res_4862_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4863_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4864_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4865_: *mut crate::leanh::LeanObject,
    mut v_ext_4866_: *mut crate::leanh::LeanObject,
    mut v_as_4867_: *mut crate::leanh::LeanObject,
    mut v_sz_4868_: usize,
    mut v_i_4869_: usize,
    mut v_b_4870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_4866_, v_as_4867_, v_sz_4868_, v_i_4869_, v_b_4870_);
    return v___x_4871_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_4872_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4873_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4874_: *mut crate::leanh::LeanObject,
    mut v_ext_4875_: *mut crate::leanh::LeanObject,
    mut v_as_4876_: *mut crate::leanh::LeanObject,
    mut v_sz_4877_: *mut crate::leanh::LeanObject,
    mut v_i_4878_: *mut crate::leanh::LeanObject,
    mut v_b_4879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4880_: usize = 0;
    let mut v_i_boxed_4881_: usize = 0;
    let mut v_res_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4880_ = crate::leanh::lean_unbox_usize(v_sz_4877_);
    crate::leanh::lean_dec(v_sz_4877_);
    v_i_boxed_4881_ = crate::leanh::lean_unbox_usize(v_i_4878_);
    crate::leanh::lean_dec(v_i_4878_);
    v_res_4882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_4872_, v_00_u03c3_4873_, v_00_u03b1_4874_, v_ext_4875_, v_as_4876_, v_sz_boxed_4880_, v_i_boxed_4881_, v_b_4879_);
    crate::leanh::lean_dec_ref(v_as_4876_);
    return v_res_4882_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(
    mut v_00_u03b2_4883_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4884_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4885_: *mut crate::leanh::LeanObject,
    mut v_ext_4886_: *mut crate::leanh::LeanObject,
    mut v_as_4887_: *mut crate::leanh::LeanObject,
    mut v_sz_4888_: usize,
    mut v_i_4889_: usize,
    mut v_b_4890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_4886_, v_as_4887_, v_sz_4888_, v_i_4889_, v_b_4890_);
    return v___x_4891_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_4892_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4893_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4894_: *mut crate::leanh::LeanObject,
    mut v_ext_4895_: *mut crate::leanh::LeanObject,
    mut v_as_4896_: *mut crate::leanh::LeanObject,
    mut v_sz_4897_: *mut crate::leanh::LeanObject,
    mut v_i_4898_: *mut crate::leanh::LeanObject,
    mut v_b_4899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4900_: usize = 0;
    let mut v_i_boxed_4901_: usize = 0;
    let mut v_res_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4900_ = crate::leanh::lean_unbox_usize(v_sz_4897_);
    crate::leanh::lean_dec(v_sz_4897_);
    v_i_boxed_4901_ = crate::leanh::lean_unbox_usize(v_i_4898_);
    crate::leanh::lean_dec(v_i_4898_);
    v_res_4902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_4892_, v_00_u03c3_4893_, v_00_u03b1_4894_, v_ext_4895_, v_as_4896_, v_sz_boxed_4900_, v_i_boxed_4901_, v_b_4899_);
    crate::leanh::lean_dec_ref(v_as_4896_);
    return v_res_4902_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_4903_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4904_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4905_: *mut crate::leanh::LeanObject,
    mut v_ext_4906_: *mut crate::leanh::LeanObject,
    mut v_as_4907_: *mut crate::leanh::LeanObject,
    mut v_sz_4908_: usize,
    mut v_i_4909_: usize,
    mut v_b_4910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_4906_, v_as_4907_, v_sz_4908_, v_i_4909_, v_b_4910_);
    return v___x_4911_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_00_u03b2_4912_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4913_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4914_: *mut crate::leanh::LeanObject,
    mut v_ext_4915_: *mut crate::leanh::LeanObject,
    mut v_as_4916_: *mut crate::leanh::LeanObject,
    mut v_sz_4917_: *mut crate::leanh::LeanObject,
    mut v_i_4918_: *mut crate::leanh::LeanObject,
    mut v_b_4919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4920_: usize = 0;
    let mut v_i_boxed_4921_: usize = 0;
    let mut v_res_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4920_ = crate::leanh::lean_unbox_usize(v_sz_4917_);
    crate::leanh::lean_dec(v_sz_4917_);
    v_i_boxed_4921_ = crate::leanh::lean_unbox_usize(v_i_4918_);
    crate::leanh::lean_dec(v_i_4918_);
    v_res_4922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_4912_, v_00_u03c3_4913_, v_00_u03b1_4914_, v_ext_4915_, v_as_4916_, v_sz_boxed_4920_, v_i_boxed_4921_, v_b_4919_);
    crate::leanh::lean_dec_ref(v_as_4916_);
    return v_res_4922_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(
    mut v_f_4923_: *mut crate::leanh::LeanObject,
    mut v_s_4924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stateStack_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4931_: u8 = 0;
    let mut v_tail_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v_state_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_4938_: u8 = 0;
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4952_: u8 = 0;
    let mut v_isSharedCheck_4953_: u8 = 0;
    let mut v_unused_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4955_: u8 = 0;
    let mut v_unused_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4925_ = crate::leanh::lean_ctor_get(v_s_4924_, 0);
                crate::leanh::lean_inc(v_stateStack_4925_);
                if crate::leanh::lean_obj_tag(v_stateStack_4925_) == 1 {
                    v_head_4926_ = crate::leanh::lean_ctor_get(v_stateStack_4925_, 0);
                    crate::leanh::lean_inc(v_head_4926_);
                    v_scopedEntries_4927_ = crate::leanh::lean_ctor_get(v_s_4924_, 1);
                    v_newEntries_4928_ = crate::leanh::lean_ctor_get(v_s_4924_, 2);
                    v_isSharedCheck_4955_ = (!crate::leanh::lean_is_exclusive(v_s_4924_)) as u8;
                    if v_isSharedCheck_4955_ == 0 {
                        v_unused_4956_ = crate::leanh::lean_ctor_get(v_s_4924_, 0);
                        crate::leanh::lean_dec(v_unused_4956_);
                        v___x_4930_ = v_s_4924_;
                        v_isShared_4931_ = v_isSharedCheck_4955_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_newEntries_4928_);
                        crate::leanh::lean_inc(v_scopedEntries_4927_);
                        crate::leanh::lean_dec(v_s_4924_);
                        v___x_4930_ = crate::leanh::lean_box(0);
                        v_isShared_4931_ = v_isSharedCheck_4955_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stateStack_4925_);
                    crate::leanh::lean_dec(v_f_4923_);
                    return v_s_4924_;
                }
            }
            1 => {
                v_tail_4932_ = crate::leanh::lean_ctor_get(v_stateStack_4925_, 1);
                v_isSharedCheck_4953_ =
                    (!crate::leanh::lean_is_exclusive(v_stateStack_4925_)) as u8;
                if v_isSharedCheck_4953_ == 0 {
                    v_unused_4954_ = crate::leanh::lean_ctor_get(v_stateStack_4925_, 0);
                    crate::leanh::lean_dec(v_unused_4954_);
                    v___x_4934_ = v_stateStack_4925_;
                    v_isShared_4935_ = v_isSharedCheck_4953_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tail_4932_);
                    crate::leanh::lean_dec(v_stateStack_4925_);
                    v___x_4934_ = crate::leanh::lean_box(0);
                    v_isShared_4935_ = v_isSharedCheck_4953_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_state_4936_ = crate::leanh::lean_ctor_get(v_head_4926_, 0);
                v_activeScopes_4937_ = crate::leanh::lean_ctor_get(v_head_4926_, 1);
                v_delimitsLocal_4938_ = crate::leanh::lean_ctor_get_uint8(
                    v_head_4926_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_4952_ = (!crate::leanh::lean_is_exclusive(v_head_4926_)) as u8;
                if v_isSharedCheck_4952_ == 0 {
                    v___x_4940_ = v_head_4926_;
                    v_isShared_4941_ = v_isSharedCheck_4952_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_activeScopes_4937_);
                    crate::leanh::lean_inc(v_state_4936_);
                    crate::leanh::lean_dec(v_head_4926_);
                    v___x_4940_ = crate::leanh::lean_box(0);
                    v_isShared_4941_ = v_isSharedCheck_4952_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4942_ = crate::leanh::lean_apply_1(v_f_4923_, v_state_4936_);
                if v_isShared_4941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4940_, 0, v___x_4942_);
                    v___x_4944_ = v___x_4940_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4951_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_activeScopes_4937_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4951_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_delimitsLocal_4938_,
                    );
                    v___x_4944_ = v_reuseFailAlloc_4951_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4935_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4934_, 0, v___x_4944_);
                    v___x_4946_ = v___x_4934_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4950_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4950_, 1, v_tail_4932_);
                    v___x_4946_ = v_reuseFailAlloc_4950_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4930_, 0, v___x_4946_);
                    v___x_4948_ = v___x_4930_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4949_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_scopedEntries_4927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4949_, 2, v_newEntries_4928_);
                    v___x_4948_ = v_reuseFailAlloc_4949_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_modifyState___redArg(
    mut v_ext_4957_: *mut crate::leanh::LeanObject,
    mut v_env_4958_: *mut crate::leanh::LeanObject,
    mut v_f_4959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ext_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ext_4960_ = crate::leanh::lean_ctor_get(v_ext_4957_, 1);
    crate::leanh::lean_inc_ref(v_ext_4960_);
    crate::leanh::lean_dec_ref(v_ext_4957_);
    v_toEnvExtension_4961_ = crate::leanh::lean_ctor_get(v_ext_4960_, 0);
    v_asyncMode_4962_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4961_, 2);
    crate::leanh::lean_inc(v_asyncMode_4962_);
    v___f_4963_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4963_, 0, v_f_4959_);
    v___x_4964_ = crate::leanh::lean_box(0);
    v___x_4965_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4960_,
        v_env_4958_,
        v___f_4963_,
        v_asyncMode_4962_,
        v___x_4964_,
    );
    crate::leanh::lean_dec(v_asyncMode_4962_);
    return v___x_4965_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_modifyState(
    mut v_00_u03b1_4966_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4967_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4968_: *mut crate::leanh::LeanObject,
    mut v_ext_4969_: *mut crate::leanh::LeanObject,
    mut v_env_4970_: *mut crate::leanh::LeanObject,
    mut v_f_4971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4972_ =
        l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_4969_, v_env_4970_, v_f_4971_);
    return v___x_4972_;
}
pub unsafe fn l_Lean_pushScope___redArg___lam__0(
    mut v_toPure_4973_: *mut crate::leanh::LeanObject,
    mut v_____s_4974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4975_ = crate::leanh::lean_box(0);
    v___x_4976_ =
        crate::leanh::lean_apply_2(v_toPure_4973_, crate::leanh::lean_box(0), v___x_4975_);
    return v___x_4976_;
}
pub unsafe fn l_Lean_pushScope___redArg___lam__1(
    mut v___x_4977_: *mut crate::leanh::LeanObject,
    mut v_toPure_4978_: *mut crate::leanh::LeanObject,
    mut v_r_4979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4980_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4980_, 0, v___x_4977_);
    v___x_4981_ =
        crate::leanh::lean_apply_2(v_toPure_4978_, crate::leanh::lean_box(0), v___x_4980_);
    return v___x_4981_;
}
pub unsafe fn l_Lean_pushScope___redArg___lam__2(
    mut v_inst_4982_: *mut crate::leanh::LeanObject,
    mut v_toBind_4983_: *mut crate::leanh::LeanObject,
    mut v___f_4984_: *mut crate::leanh::LeanObject,
    mut v_a_4985_: *mut crate::leanh::LeanObject,
    mut v_x_4986_: *mut crate::leanh::LeanObject,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyEnv_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_4988_ = crate::leanh::lean_ctor_get(v_inst_4982_, 1);
    crate::leanh::lean_inc(v_modifyEnv_4988_);
    crate::leanh::lean_dec_ref(v_inst_4982_);
    v___x_4989_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_pushScope as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_4989_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4989_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4989_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4989_, 3, v_a_4985_);
    v___x_4990_ = crate::leanh::lean_apply_1(v_modifyEnv_4988_, v___x_4989_);
    v___x_4991_ = crate::leanh::lean_apply_4(
        v_toBind_4983_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4990_,
        v___f_4984_,
    );
    return v___x_4991_;
}
pub unsafe fn l_Lean_pushScope___redArg___lam__3(
    mut v_toPure_4992_: *mut crate::leanh::LeanObject,
    mut v_inst_4993_: *mut crate::leanh::LeanObject,
    mut v_toBind_4994_: *mut crate::leanh::LeanObject,
    mut v_inst_4995_: *mut crate::leanh::LeanObject,
    mut v___f_4996_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5001_: usize = 0;
    let mut v___x_5002_: usize = 0;
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4998_ = crate::leanh::lean_box(0);
    v___f_4999_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4999_, 0, v___x_4998_);
    crate::leanh::lean_closure_set(v___f_4999_, 1, v_toPure_4992_);
    crate::leanh::lean_inc(v_toBind_4994_);
    v___f_5000_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5000_, 0, v_inst_4993_);
    crate::leanh::lean_closure_set(v___f_5000_, 1, v_toBind_4994_);
    crate::leanh::lean_closure_set(v___f_5000_, 2, v___f_4999_);
    v_sz_5001_ = lean_array_size(v_____do__lift_4997_);
    v___x_5002_ = 0usize;
    v___x_5003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4995_,
        v_____do__lift_4997_,
        v___f_5000_,
        v_sz_5001_,
        v___x_5002_,
        v___x_4998_,
    );
    v___x_5004_ = crate::leanh::lean_apply_4(
        v_toBind_4994_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5003_,
        v___f_4996_,
    );
    return v___x_5004_;
}
pub unsafe fn _init_l_Lean_pushScope___redArg___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5005_ = l_Lean_scopedEnvExtensionsRef;
    v___x_5006_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_5006_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5006_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5006_, 2, v___x_5005_);
    return v___x_5006_;
}
pub unsafe fn l_Lean_pushScope___redArg(
    mut v_inst_5007_: *mut crate::leanh::LeanObject,
    mut v_inst_5008_: *mut crate::leanh::LeanObject,
    mut v_inst_5009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5010_ = crate::leanh::lean_ctor_get(v_inst_5007_, 0);
    v_toBind_5011_ = crate::leanh::lean_ctor_get(v_inst_5007_, 1);
    crate::leanh::lean_inc_n(v_toBind_5011_, 2);
    v_toPure_5012_ = crate::leanh::lean_ctor_get(v_toApplicative_5010_, 1);
    crate::leanh::lean_inc_n(v_toPure_5012_, 2);
    v___x_5013_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0_once),
        _init_l_Lean_pushScope___redArg___closed__0,
    );
    v___x_5014_ = crate::leanh::lean_apply_2(v_inst_5009_, crate::leanh::lean_box(0), v___x_5013_);
    v___f_5015_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5015_, 0, v_toPure_5012_);
    v___f_5016_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_5016_, 0, v_toPure_5012_);
    crate::leanh::lean_closure_set(v___f_5016_, 1, v_inst_5008_);
    crate::leanh::lean_closure_set(v___f_5016_, 2, v_toBind_5011_);
    crate::leanh::lean_closure_set(v___f_5016_, 3, v_inst_5007_);
    crate::leanh::lean_closure_set(v___f_5016_, 4, v___f_5015_);
    v___x_5017_ = crate::leanh::lean_apply_4(
        v_toBind_5011_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5014_,
        v___f_5016_,
    );
    return v___x_5017_;
}
pub unsafe fn l_Lean_pushScope(
    mut v_m_5018_: *mut crate::leanh::LeanObject,
    mut v_inst_5019_: *mut crate::leanh::LeanObject,
    mut v_inst_5020_: *mut crate::leanh::LeanObject,
    mut v_inst_5021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5022_ = l_Lean_pushScope___redArg(v_inst_5019_, v_inst_5020_, v_inst_5021_);
    return v___x_5022_;
}
pub unsafe fn l_Lean_popScope___redArg___lam__2(
    mut v_inst_5023_: *mut crate::leanh::LeanObject,
    mut v_toBind_5024_: *mut crate::leanh::LeanObject,
    mut v___f_5025_: *mut crate::leanh::LeanObject,
    mut v_a_5026_: *mut crate::leanh::LeanObject,
    mut v_x_5027_: *mut crate::leanh::LeanObject,
    mut v___y_5028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyEnv_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_5029_ = crate::leanh::lean_ctor_get(v_inst_5023_, 1);
    crate::leanh::lean_inc(v_modifyEnv_5029_);
    crate::leanh::lean_dec_ref(v_inst_5023_);
    v___x_5030_ = crate::leanh::lean_alloc_closure(
        l_Lean_ScopedEnvExtension_popScope as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_5030_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5030_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5030_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5030_, 3, v_a_5026_);
    v___x_5031_ = crate::leanh::lean_apply_1(v_modifyEnv_5029_, v___x_5030_);
    v___x_5032_ = crate::leanh::lean_apply_4(
        v_toBind_5024_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5031_,
        v___f_5025_,
    );
    return v___x_5032_;
}
pub unsafe fn l_Lean_popScope___redArg___lam__0(
    mut v_toPure_5033_: *mut crate::leanh::LeanObject,
    mut v_inst_5034_: *mut crate::leanh::LeanObject,
    mut v_toBind_5035_: *mut crate::leanh::LeanObject,
    mut v_inst_5036_: *mut crate::leanh::LeanObject,
    mut v___f_5037_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5042_: usize = 0;
    let mut v___x_5043_: usize = 0;
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5039_ = crate::leanh::lean_box(0);
    v___f_5040_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5040_, 0, v___x_5039_);
    crate::leanh::lean_closure_set(v___f_5040_, 1, v_toPure_5033_);
    crate::leanh::lean_inc(v_toBind_5035_);
    v___f_5041_ = crate::leanh::lean_alloc_closure(
        l_Lean_popScope___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5041_, 0, v_inst_5034_);
    crate::leanh::lean_closure_set(v___f_5041_, 1, v_toBind_5035_);
    crate::leanh::lean_closure_set(v___f_5041_, 2, v___f_5040_);
    v_sz_5042_ = lean_array_size(v_____do__lift_5038_);
    v___x_5043_ = 0usize;
    v___x_5044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5036_,
        v_____do__lift_5038_,
        v___f_5041_,
        v_sz_5042_,
        v___x_5043_,
        v___x_5039_,
    );
    v___x_5045_ = crate::leanh::lean_apply_4(
        v_toBind_5035_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5044_,
        v___f_5037_,
    );
    return v___x_5045_;
}
pub unsafe fn l_Lean_popScope___redArg(
    mut v_inst_5046_: *mut crate::leanh::LeanObject,
    mut v_inst_5047_: *mut crate::leanh::LeanObject,
    mut v_inst_5048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5049_ = crate::leanh::lean_ctor_get(v_inst_5046_, 0);
    v_toBind_5050_ = crate::leanh::lean_ctor_get(v_inst_5046_, 1);
    crate::leanh::lean_inc_n(v_toBind_5050_, 2);
    v_toPure_5051_ = crate::leanh::lean_ctor_get(v_toApplicative_5049_, 1);
    crate::leanh::lean_inc_n(v_toPure_5051_, 2);
    v___x_5052_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0_once),
        _init_l_Lean_pushScope___redArg___closed__0,
    );
    v___x_5053_ = crate::leanh::lean_apply_2(v_inst_5048_, crate::leanh::lean_box(0), v___x_5052_);
    v___f_5054_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5054_, 0, v_toPure_5051_);
    v___f_5055_ = crate::leanh::lean_alloc_closure(
        l_Lean_popScope___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_5055_, 0, v_toPure_5051_);
    crate::leanh::lean_closure_set(v___f_5055_, 1, v_inst_5047_);
    crate::leanh::lean_closure_set(v___f_5055_, 2, v_toBind_5050_);
    crate::leanh::lean_closure_set(v___f_5055_, 3, v_inst_5046_);
    crate::leanh::lean_closure_set(v___f_5055_, 4, v___f_5054_);
    v___x_5056_ = crate::leanh::lean_apply_4(
        v_toBind_5050_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5053_,
        v___f_5055_,
    );
    return v___x_5056_;
}
pub unsafe fn l_Lean_popScope(
    mut v_m_5057_: *mut crate::leanh::LeanObject,
    mut v_inst_5058_: *mut crate::leanh::LeanObject,
    mut v_inst_5059_: *mut crate::leanh::LeanObject,
    mut v_inst_5060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5061_ = l_Lean_popScope___redArg(v_inst_5058_, v_inst_5059_, v_inst_5060_);
    return v___x_5061_;
}
pub unsafe fn l_Lean_setDelimitsLocal___redArg___lam__2(
    mut v_a_5062_: *mut crate::leanh::LeanObject,
    mut v_depth_5063_: *mut crate::leanh::LeanObject,
    mut v_x_5064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5065_ =
        l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_5062_, v_x_5064_, v_depth_5063_);
    return v___x_5065_;
}
pub unsafe fn l_Lean_setDelimitsLocal___redArg___lam__0(
    mut v_inst_5066_: *mut crate::leanh::LeanObject,
    mut v_depth_5067_: *mut crate::leanh::LeanObject,
    mut v_toBind_5068_: *mut crate::leanh::LeanObject,
    mut v___f_5069_: *mut crate::leanh::LeanObject,
    mut v_a_5070_: *mut crate::leanh::LeanObject,
    mut v_x_5071_: *mut crate::leanh::LeanObject,
    mut v___y_5072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyEnv_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_5073_ = crate::leanh::lean_ctor_get(v_inst_5066_, 1);
    crate::leanh::lean_inc(v_modifyEnv_5073_);
    crate::leanh::lean_dec_ref(v_inst_5066_);
    v___f_5074_ = crate::leanh::lean_alloc_closure(
        l_Lean_setDelimitsLocal___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5074_, 0, v_a_5070_);
    crate::leanh::lean_closure_set(v___f_5074_, 1, v_depth_5067_);
    v___x_5075_ = crate::leanh::lean_apply_1(v_modifyEnv_5073_, v___f_5074_);
    v___x_5076_ = crate::leanh::lean_apply_4(
        v_toBind_5068_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5075_,
        v___f_5069_,
    );
    return v___x_5076_;
}
pub unsafe fn l_Lean_setDelimitsLocal___redArg___lam__1(
    mut v_toPure_5077_: *mut crate::leanh::LeanObject,
    mut v_inst_5078_: *mut crate::leanh::LeanObject,
    mut v_depth_5079_: *mut crate::leanh::LeanObject,
    mut v_toBind_5080_: *mut crate::leanh::LeanObject,
    mut v_inst_5081_: *mut crate::leanh::LeanObject,
    mut v___f_5082_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5087_: usize = 0;
    let mut v___x_5088_: usize = 0;
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5084_ = crate::leanh::lean_box(0);
    v___f_5085_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5085_, 0, v___x_5084_);
    crate::leanh::lean_closure_set(v___f_5085_, 1, v_toPure_5077_);
    crate::leanh::lean_inc(v_toBind_5080_);
    v___f_5086_ = crate::leanh::lean_alloc_closure(
        l_Lean_setDelimitsLocal___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5086_, 0, v_inst_5078_);
    crate::leanh::lean_closure_set(v___f_5086_, 1, v_depth_5079_);
    crate::leanh::lean_closure_set(v___f_5086_, 2, v_toBind_5080_);
    crate::leanh::lean_closure_set(v___f_5086_, 3, v___f_5085_);
    v_sz_5087_ = lean_array_size(v_____do__lift_5083_);
    v___x_5088_ = 0usize;
    v___x_5089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5081_,
        v_____do__lift_5083_,
        v___f_5086_,
        v_sz_5087_,
        v___x_5088_,
        v___x_5084_,
    );
    v___x_5090_ = crate::leanh::lean_apply_4(
        v_toBind_5080_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5089_,
        v___f_5082_,
    );
    return v___x_5090_;
}
pub unsafe fn l_Lean_setDelimitsLocal___redArg(
    mut v_inst_5091_: *mut crate::leanh::LeanObject,
    mut v_inst_5092_: *mut crate::leanh::LeanObject,
    mut v_inst_5093_: *mut crate::leanh::LeanObject,
    mut v_depth_5094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5095_ = crate::leanh::lean_ctor_get(v_inst_5091_, 0);
    v_toBind_5096_ = crate::leanh::lean_ctor_get(v_inst_5091_, 1);
    crate::leanh::lean_inc_n(v_toBind_5096_, 2);
    v_toPure_5097_ = crate::leanh::lean_ctor_get(v_toApplicative_5095_, 1);
    crate::leanh::lean_inc_n(v_toPure_5097_, 2);
    v___x_5098_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0_once),
        _init_l_Lean_pushScope___redArg___closed__0,
    );
    v___x_5099_ = crate::leanh::lean_apply_2(v_inst_5093_, crate::leanh::lean_box(0), v___x_5098_);
    v___f_5100_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5100_, 0, v_toPure_5097_);
    v___f_5101_ = crate::leanh::lean_alloc_closure(
        l_Lean_setDelimitsLocal___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_5101_, 0, v_toPure_5097_);
    crate::leanh::lean_closure_set(v___f_5101_, 1, v_inst_5092_);
    crate::leanh::lean_closure_set(v___f_5101_, 2, v_depth_5094_);
    crate::leanh::lean_closure_set(v___f_5101_, 3, v_toBind_5096_);
    crate::leanh::lean_closure_set(v___f_5101_, 4, v_inst_5091_);
    crate::leanh::lean_closure_set(v___f_5101_, 5, v___f_5100_);
    v___x_5102_ = crate::leanh::lean_apply_4(
        v_toBind_5096_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5099_,
        v___f_5101_,
    );
    return v___x_5102_;
}
pub unsafe fn l_Lean_setDelimitsLocal(
    mut v_m_5103_: *mut crate::leanh::LeanObject,
    mut v_inst_5104_: *mut crate::leanh::LeanObject,
    mut v_inst_5105_: *mut crate::leanh::LeanObject,
    mut v_inst_5106_: *mut crate::leanh::LeanObject,
    mut v_depth_5107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5108_ =
        l_Lean_setDelimitsLocal___redArg(v_inst_5104_, v_inst_5105_, v_inst_5106_, v_depth_5107_);
    return v___x_5108_;
}
pub unsafe fn l_Lean_activateScoped___redArg___lam__2(
    mut v_a_5109_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_5110_: *mut crate::leanh::LeanObject,
    mut v_x_5111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5112_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(
        v_a_5109_,
        v_x_5111_,
        v_namespaceName_5110_,
    );
    return v___x_5112_;
}
pub unsafe fn l_Lean_activateScoped___redArg___lam__0(
    mut v_inst_5113_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_5114_: *mut crate::leanh::LeanObject,
    mut v_toBind_5115_: *mut crate::leanh::LeanObject,
    mut v___f_5116_: *mut crate::leanh::LeanObject,
    mut v_a_5117_: *mut crate::leanh::LeanObject,
    mut v_x_5118_: *mut crate::leanh::LeanObject,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyEnv_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_5120_ = crate::leanh::lean_ctor_get(v_inst_5113_, 1);
    crate::leanh::lean_inc(v_modifyEnv_5120_);
    crate::leanh::lean_dec_ref(v_inst_5113_);
    v___f_5121_ = crate::leanh::lean_alloc_closure(
        l_Lean_activateScoped___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5121_, 0, v_a_5117_);
    crate::leanh::lean_closure_set(v___f_5121_, 1, v_namespaceName_5114_);
    v___x_5122_ = crate::leanh::lean_apply_1(v_modifyEnv_5120_, v___f_5121_);
    v___x_5123_ = crate::leanh::lean_apply_4(
        v_toBind_5115_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5122_,
        v___f_5116_,
    );
    return v___x_5123_;
}
pub unsafe fn l_Lean_activateScoped___redArg___lam__1(
    mut v_toPure_5124_: *mut crate::leanh::LeanObject,
    mut v_inst_5125_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_5126_: *mut crate::leanh::LeanObject,
    mut v_toBind_5127_: *mut crate::leanh::LeanObject,
    mut v_inst_5128_: *mut crate::leanh::LeanObject,
    mut v___f_5129_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5134_: usize = 0;
    let mut v___x_5135_: usize = 0;
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5131_ = crate::leanh::lean_box(0);
    v___f_5132_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5132_, 0, v___x_5131_);
    crate::leanh::lean_closure_set(v___f_5132_, 1, v_toPure_5124_);
    crate::leanh::lean_inc(v_toBind_5127_);
    v___f_5133_ = crate::leanh::lean_alloc_closure(
        l_Lean_activateScoped___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5133_, 0, v_inst_5125_);
    crate::leanh::lean_closure_set(v___f_5133_, 1, v_namespaceName_5126_);
    crate::leanh::lean_closure_set(v___f_5133_, 2, v_toBind_5127_);
    crate::leanh::lean_closure_set(v___f_5133_, 3, v___f_5132_);
    v_sz_5134_ = lean_array_size(v_____do__lift_5130_);
    v___x_5135_ = 0usize;
    v___x_5136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5128_,
        v_____do__lift_5130_,
        v___f_5133_,
        v_sz_5134_,
        v___x_5135_,
        v___x_5131_,
    );
    v___x_5137_ = crate::leanh::lean_apply_4(
        v_toBind_5127_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5136_,
        v___f_5129_,
    );
    return v___x_5137_;
}
pub unsafe fn l_Lean_activateScoped___redArg(
    mut v_inst_5138_: *mut crate::leanh::LeanObject,
    mut v_inst_5139_: *mut crate::leanh::LeanObject,
    mut v_inst_5140_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_5141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5142_ = crate::leanh::lean_ctor_get(v_inst_5138_, 0);
    v_toBind_5143_ = crate::leanh::lean_ctor_get(v_inst_5138_, 1);
    crate::leanh::lean_inc_n(v_toBind_5143_, 2);
    v_toPure_5144_ = crate::leanh::lean_ctor_get(v_toApplicative_5142_, 1);
    crate::leanh::lean_inc_n(v_toPure_5144_, 2);
    v___x_5145_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0_once),
        _init_l_Lean_pushScope___redArg___closed__0,
    );
    v___x_5146_ = crate::leanh::lean_apply_2(v_inst_5140_, crate::leanh::lean_box(0), v___x_5145_);
    v___f_5147_ = crate::leanh::lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5147_, 0, v_toPure_5144_);
    v___f_5148_ = crate::leanh::lean_alloc_closure(
        l_Lean_activateScoped___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_5148_, 0, v_toPure_5144_);
    crate::leanh::lean_closure_set(v___f_5148_, 1, v_inst_5139_);
    crate::leanh::lean_closure_set(v___f_5148_, 2, v_namespaceName_5141_);
    crate::leanh::lean_closure_set(v___f_5148_, 3, v_toBind_5143_);
    crate::leanh::lean_closure_set(v___f_5148_, 4, v_inst_5138_);
    crate::leanh::lean_closure_set(v___f_5148_, 5, v___f_5147_);
    v___x_5149_ = crate::leanh::lean_apply_4(
        v_toBind_5143_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5146_,
        v___f_5148_,
    );
    return v___x_5149_;
}
pub unsafe fn l_Lean_activateScoped(
    mut v_m_5150_: *mut crate::leanh::LeanObject,
    mut v_inst_5151_: *mut crate::leanh::LeanObject,
    mut v_inst_5152_: *mut crate::leanh::LeanObject,
    mut v_inst_5153_: *mut crate::leanh::LeanObject,
    mut v_namespaceName_5154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5155_ = l_Lean_activateScoped___redArg(
        v_inst_5151_,
        v_inst_5152_,
        v_inst_5153_,
        v_namespaceName_5154_,
    );
    return v___x_5155_;
}
pub unsafe fn _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5156_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28,
    );
    return v___x_5156_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(
    mut v___y_5157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___y_5157_);
    return v___y_5157_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(
    mut v___y_5158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5159_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_5158_);
    crate::leanh::lean_dec(v___y_5158_);
    return v_res_5159_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(
    mut v_x_5160_: *mut crate::leanh::LeanObject,
    mut v_a_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5164_, 0, v_a_5161_);
    return v___x_5164_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(
    mut v_x_5165_: *mut crate::leanh::LeanObject,
    mut v_a_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
    mut v___y_5168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5169_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(
        v_x_5165_,
        v_a_5166_,
        v___y_5167_,
    );
    crate::leanh::lean_dec_ref(v___y_5167_);
    crate::leanh::lean_dec(v_x_5165_);
    return v_res_5169_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(
    mut v_initial_5170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5172_, 0, v_initial_5170_);
    return v___x_5172_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(
    mut v_initial_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_5173_);
    return v_res_5175_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg(
    mut v_descr_5178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addEntry_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initial_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_finalizeImport_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exportEntry_x3f_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5180_ = crate::leanh::lean_ctor_get(v_descr_5178_, 0);
    crate::leanh::lean_inc(v_name_5180_);
    v_addEntry_5181_ = crate::leanh::lean_ctor_get(v_descr_5178_, 1);
    crate::leanh::lean_inc(v_addEntry_5181_);
    v_initial_5182_ = crate::leanh::lean_ctor_get(v_descr_5178_, 2);
    crate::leanh::lean_inc(v_initial_5182_);
    v_finalizeImport_5183_ = crate::leanh::lean_ctor_get(v_descr_5178_, 3);
    crate::leanh::lean_inc(v_finalizeImport_5183_);
    v_exportEntry_x3f_5184_ = crate::leanh::lean_ctor_get(v_descr_5178_, 4);
    crate::leanh::lean_inc_ref(v_exportEntry_x3f_5184_);
    crate::leanh::lean_dec_ref(v_descr_5178_);
    v___f_5185_ = l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0;
    v___f_5186_ = l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1;
    v___f_5187_ = crate::leanh::lean_alloc_closure(
        l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5187_, 0, v_initial_5182_);
    v___x_5188_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5188_, 0, v_name_5180_);
    crate::leanh::lean_ctor_set(v___x_5188_, 1, v___f_5187_);
    crate::leanh::lean_ctor_set(v___x_5188_, 2, v___f_5186_);
    crate::leanh::lean_ctor_set(v___x_5188_, 3, v___f_5185_);
    crate::leanh::lean_ctor_set(v___x_5188_, 4, v_addEntry_5181_);
    crate::leanh::lean_ctor_set(v___x_5188_, 5, v_finalizeImport_5183_);
    crate::leanh::lean_ctor_set(v___x_5188_, 6, v_exportEntry_x3f_5184_);
    v___x_5189_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_5188_);
    return v___x_5189_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(
    mut v_descr_5190_: *mut crate::leanh::LeanObject,
    mut v_a_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5192_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_5190_);
    return v_res_5192_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension(
    mut v_00_u03b1_5193_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5194_: *mut crate::leanh::LeanObject,
    mut v_descr_5195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5197_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_5195_);
    return v___x_5197_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___boxed(
    mut v_00_u03b1_5198_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_5199_: *mut crate::leanh::LeanObject,
    mut v_descr_5200_: *mut crate::leanh::LeanObject,
    mut v_a_5201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5202_ =
        l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_5198_, v_00_u03c3_5199_, v_descr_5200_);
    return v_res_5202_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ScopedEnvExtension(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_scopedEnvExtensionsRef = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_scopedEnvExtensionsRef);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ScopedEnvExtension(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_ScopedEnvExtension_Descr_name___autoParam =
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_ScopedEnvExtension_Descr_name___autoParam);
    l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam =
        _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam();
    crate::leanh::lean_mark_persistent(l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ScopedEnvExtension(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ScopedEnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_ScopedEnvExtension(builtin);
}

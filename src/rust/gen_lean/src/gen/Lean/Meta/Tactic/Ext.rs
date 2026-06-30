// Lean compiler output
// Module: Lean.Meta.Tactic.Ext
// Imports: Init.Data.Array.InsertionSort Lean.Meta.DiscrTree
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set,
    lean_array_to_list, lean_array_uget_borrowed, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub, lean_nat_to_int,
    lean_panic_fn_borrowed, lean_st_ref_get, lean_string_length, lean_uint64_mix_hash,
    lean_uint64_of_nat, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop, l_Array_eraseIdx___redArg,
    l_Array_reverse___redArg,
};
use crate::r#gen::Init::Data::Array::InsertionSort::{
    initialize_Init_Data_Array_InsertionSort,
    l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse,
    runtime_initialize_Init_Data_Array_InsertionSort,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_contains___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_isUnaryNode___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofConstName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes,
    l_Lean_Meta_DiscrTree_Key_lt, l_Lean_Meta_DiscrTree_instInhabited,
};
use crate::r#gen::Lean::Meta::DiscrTree::Main::l_Lean_Meta_DiscrTree_getMatch___redArg;
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
    l_Lean_Meta_DiscrTree_instReprKey_repr,
};
use crate::r#gen::Lean::Meta::DiscrTree::{
    initialize_Lean_Meta_DiscrTree, runtime_initialize_Lean_Meta_DiscrTree,
};
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_getState___redArg, l_Lean_registerSimpleScopedEnvExtension___redArg,
};
pub static l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__0_value:
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
static mut l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Ext_instInhabitedExtTheorem_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Ext_instInhabitedExtTheorem: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0_value:
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
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__1_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__3_value:
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
        core::ptr::addr_of!(
            l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__4_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__9_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__9_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__1_value:
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
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__3_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__8_value:
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
    m_data: [112, 114, 105, 111, 114, 105, 116, 121, 0],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__10_value:
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
    m_data: [107, 101, 121, 115, 0],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__13_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instReprExtTheorem___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_Ext_instReprExtTheorem_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Ext_instReprExtTheorem___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Ext_instReprExtTheorem: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instReprExtTheorem___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_instBEqExtTheorem___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Ext_instBEqExtTheorem_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_instBEqExtTheorem___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instBEqExtTheorem___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Ext_instBEqExtTheorem: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instBEqExtTheorem___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0: u64 = 0;
pub static l_Lean_Meta_Ext_instHashableExtTheorem___closed__0_value:
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
    m_fun: l_Lean_Meta_Ext_instHashableExtTheorem_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Ext_instHashableExtTheorem___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instHashableExtTheorem___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Ext_instHashableExtTheorem: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_instHashableExtTheorem___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Ext_instInhabitedExtTheorems_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Ext_instInhabitedExtTheorems: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1: usize = 0;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__3_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__3_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__3_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__4_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__4_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__4_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__5_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__5_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__5_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__6_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__6_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__6_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__3_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__4_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__5_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1095896425108153958 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__6_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2035546098643888083 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Ext_extExtension: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Ext_getExtTheorems___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__7_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__9_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__11_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Ext_getExtTheorems___closed__12_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Ext_getExtTheorems___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_getExtTheorems___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 101, 114, 97, 115, 101, 32, 96, 91, 101, 120, 116, 93, 96,
        32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 102, 114, 111, 109, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        96, 58, 32, 73, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32,
        116, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__1(
    mut v_a_1788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1789_ = lean_nat_to_int(v_a_1788_);
    return v___x_1789_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0___lam__0(
    mut v___y_1790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = leanh::lean_unsigned_to_nat(0);
    v___x_1792_ = l_Lean_Meta_DiscrTree_instReprKey_repr(v___y_1790_, v___x_1791_);
    return v___x_1792_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_1793_: *mut leanh::LeanObject,
    mut v_x_1794_: *mut leanh::LeanObject,
    mut v_x_1795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1795_) == 0 {
                    leanh::lean_dec(v_x_1793_);
                    return v_x_1794_;
                } else {
                    v_head_1796_ = leanh::lean_ctor_get(v_x_1795_, 0);
                    v_tail_1797_ = leanh::lean_ctor_get(v_x_1795_, 1);
                    v_isSharedCheck_1808_ = (!leanh::lean_is_exclusive(v_x_1795_)) as u8;
                    if v_isSharedCheck_1808_ == 0 {
                        v___x_1799_ = v_x_1795_;
                        v_isShared_1800_ = v_isSharedCheck_1808_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1797_);
                        leanh::lean_inc(v_head_1796_);
                        leanh::lean_dec(v_x_1795_);
                        v___x_1799_ = leanh::lean_box(0);
                        v_isShared_1800_ = v_isSharedCheck_1808_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1793_);
                if v_isShared_1800_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1799_, 5);
                    leanh::lean_ctor_set(v___x_1799_, 1, v_x_1793_);
                    leanh::lean_ctor_set(v___x_1799_, 0, v_x_1794_);
                    v___x_1802_ = v___x_1799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_x_1794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_x_1793_);
                    v___x_1802_ = v_reuseFailAlloc_1807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1803_ = leanh::lean_unsigned_to_nat(0);
                v___x_1804_ = l_Lean_Meta_DiscrTree_instReprKey_repr(v_head_1796_, v___x_1803_);
                v___x_1805_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1805_, 0, v___x_1802_);
                leanh::lean_ctor_set(v___x_1805_, 1, v___x_1804_);
                v_x_1794_ = v___x_1805_;
                v_x_1795_ = v_tail_1797_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2(
    mut v_x_1809_: *mut leanh::LeanObject,
    mut v_x_1810_: *mut leanh::LeanObject,
    mut v_x_1811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1811_) == 0 {
                    leanh::lean_dec(v_x_1809_);
                    return v_x_1810_;
                } else {
                    v_head_1812_ = leanh::lean_ctor_get(v_x_1811_, 0);
                    v_tail_1813_ = leanh::lean_ctor_get(v_x_1811_, 1);
                    v_isSharedCheck_1824_ = (!leanh::lean_is_exclusive(v_x_1811_)) as u8;
                    if v_isSharedCheck_1824_ == 0 {
                        v___x_1815_ = v_x_1811_;
                        v_isShared_1816_ = v_isSharedCheck_1824_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1813_);
                        leanh::lean_inc(v_head_1812_);
                        leanh::lean_dec(v_x_1811_);
                        v___x_1815_ = leanh::lean_box(0);
                        v_isShared_1816_ = v_isSharedCheck_1824_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1809_);
                if v_isShared_1816_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1815_, 5);
                    leanh::lean_ctor_set(v___x_1815_, 1, v_x_1809_);
                    leanh::lean_ctor_set(v___x_1815_, 0, v_x_1810_);
                    v___x_1818_ = v___x_1815_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1823_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_x_1810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_x_1809_);
                    v___x_1818_ = v_reuseFailAlloc_1823_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1819_ = leanh::lean_unsigned_to_nat(0);
                v___x_1820_ = l_Lean_Meta_DiscrTree_instReprKey_repr(v_head_1812_, v___x_1819_);
                v___x_1821_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1821_, 0, v___x_1818_);
                leanh::lean_ctor_set(v___x_1821_, 1, v___x_1820_);
                v___x_1822_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2_spec__3(v_x_1809_, v___x_1821_, v_tail_1813_);
                return v___x_1822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0(
    mut v_x_1825_: *mut leanh::LeanObject,
    mut v_x_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1825_) == 0 {
        let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1826_);
        v___x_1827_ = leanh::lean_box(0);
        return v___x_1827_;
    } else {
        let mut v_tail_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1828_ = leanh::lean_ctor_get(v_x_1825_, 1);
        if leanh::lean_obj_tag(v_tail_1828_) == 0 {
            let mut v_head_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1826_);
            v_head_1829_ = leanh::lean_ctor_get(v_x_1825_, 0);
            leanh::lean_inc(v_head_1829_);
            leanh::lean_dec_ref_known(v_x_1825_, 2);
            v___x_1830_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0___lam__0(v_head_1829_);
            return v___x_1830_;
        } else {
            let mut v_head_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1828_);
            v_head_1831_ = leanh::lean_ctor_get(v_x_1825_, 0);
            leanh::lean_inc(v_head_1831_);
            leanh::lean_dec_ref_known(v_x_1825_, 2);
            v___x_1832_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0___lam__0(v_head_1831_);
            v___x_1833_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2(v_x_1826_, v___x_1832_, v_tail_1828_);
            return v___x_1833_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0;
    v___x_1843_ = lean_string_length(v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1844_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5_once
        ),
        _init_l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5,
    );
    v___x_1845_ = lean_nat_to_int(v___x_1844_);
    return v___x_1845_;
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0(
    mut v_xs_1853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    v___x_1854_ = lean_array_get_size(v_xs_1853_);
    v___x_1855_ = leanh::lean_unsigned_to_nat(0);
    v___x_1856_ = lean_nat_dec_eq(v___x_1854_, v___x_1855_);
    if v___x_1856_ == 0 {
        let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1857_ = lean_array_to_list(v_xs_1853_);
        v___x_1858_ =
            l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__3;
        v___x_1859_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0(v___x_1857_, v___x_1858_);
        v___x_1860_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6);
        v___x_1861_ =
            l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__7;
        v___x_1862_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
        leanh::lean_ctor_set(v___x_1862_, 1, v___x_1859_);
        v___x_1863_ =
            l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__8;
        v___x_1864_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1864_, 0, v___x_1862_);
        leanh::lean_ctor_set(v___x_1864_, 1, v___x_1863_);
        v___x_1865_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1865_, 0, v___x_1860_);
        leanh::lean_ctor_set(v___x_1865_, 1, v___x_1864_);
        v___x_1866_ = l_Std_Format_fill(v___x_1865_);
        return v___x_1866_;
    } else {
        let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1853_);
        v___x_1867_ =
            l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__10;
        return v___x_1867_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1881_ = leanh::lean_unsigned_to_nat(12);
    v___x_1882_ = lean_nat_to_int(v___x_1881_);
    return v___x_1882_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1889_ = leanh::lean_unsigned_to_nat(8);
    v___x_1890_ = lean_nat_to_int(v___x_1889_);
    return v___x_1890_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0;
    v___x_1893_ = lean_string_length(v___x_1892_);
    return v___x_1893_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14_once),
        _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14,
    );
    v___x_1895_ = lean_nat_to_int(v___x_1894_);
    return v___x_1895_;
}
pub unsafe fn l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg(
    mut v_x_1900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: u8 = 0;
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_declName_1901_ = leanh::lean_ctor_get(v_x_1900_, 0);
    leanh::lean_inc(v_declName_1901_);
    v_priority_1902_ = leanh::lean_ctor_get(v_x_1900_, 1);
    leanh::lean_inc(v_priority_1902_);
    v_keys_1903_ = leanh::lean_ctor_get(v_x_1900_, 2);
    leanh::lean_inc_ref(v_keys_1903_);
    leanh::lean_dec_ref(v_x_1900_);
    v___x_1904_ = l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5;
    v___x_1905_ = l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__6;
    v___x_1906_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7,
    );
    v___x_1907_ = leanh::lean_unsigned_to_nat(0);
    v___x_1908_ = l_Lean_Name_reprPrec(v_declName_1901_, v___x_1907_);
    v___x_1909_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1909_, 0, v___x_1906_);
    leanh::lean_ctor_set(v___x_1909_, 1, v___x_1908_);
    v___x_1910_ = 0;
    v___x_1911_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1911_, 0, v___x_1909_);
    leanh::lean_ctor_set_uint8(
        v___x_1911_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1910_,
    );
    v___x_1912_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1912_, 0, v___x_1905_);
    leanh::lean_ctor_set(v___x_1912_, 1, v___x_1911_);
    v___x_1913_ = l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2;
    v___x_1914_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1914_, 0, v___x_1912_);
    leanh::lean_ctor_set(v___x_1914_, 1, v___x_1913_);
    v___x_1915_ = leanh::lean_box(1);
    v___x_1916_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1916_, 0, v___x_1914_);
    leanh::lean_ctor_set(v___x_1916_, 1, v___x_1915_);
    v___x_1917_ = l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__9;
    v___x_1918_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1918_, 0, v___x_1916_);
    leanh::lean_ctor_set(v___x_1918_, 1, v___x_1917_);
    v___x_1919_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1919_, 0, v___x_1918_);
    leanh::lean_ctor_set(v___x_1919_, 1, v___x_1904_);
    v___x_1920_ = l_Nat_reprFast(v_priority_1902_);
    v___x_1921_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1921_, 0, v___x_1920_);
    v___x_1922_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1922_, 0, v___x_1906_);
    leanh::lean_ctor_set(v___x_1922_, 1, v___x_1921_);
    v___x_1923_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1923_, 0, v___x_1922_);
    leanh::lean_ctor_set_uint8(
        v___x_1923_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1910_,
    );
    v___x_1924_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1924_, 0, v___x_1919_);
    leanh::lean_ctor_set(v___x_1924_, 1, v___x_1923_);
    v___x_1925_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
    leanh::lean_ctor_set(v___x_1925_, 1, v___x_1913_);
    v___x_1926_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1926_, 0, v___x_1925_);
    leanh::lean_ctor_set(v___x_1926_, 1, v___x_1915_);
    v___x_1927_ = l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__11;
    v___x_1928_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1928_, 0, v___x_1926_);
    leanh::lean_ctor_set(v___x_1928_, 1, v___x_1927_);
    v___x_1929_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1929_, 0, v___x_1928_);
    leanh::lean_ctor_set(v___x_1929_, 1, v___x_1904_);
    v___x_1930_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12_once),
        _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12,
    );
    v___x_1931_ = l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0(v_keys_1903_);
    v___x_1932_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1932_, 0, v___x_1930_);
    leanh::lean_ctor_set(v___x_1932_, 1, v___x_1931_);
    v___x_1933_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1933_, 0, v___x_1932_);
    leanh::lean_ctor_set_uint8(
        v___x_1933_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1910_,
    );
    v___x_1934_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1934_, 0, v___x_1929_);
    leanh::lean_ctor_set(v___x_1934_, 1, v___x_1933_);
    v___x_1935_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15_once),
        _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15,
    );
    v___x_1936_ = l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__16;
    v___x_1937_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1937_, 0, v___x_1936_);
    leanh::lean_ctor_set(v___x_1937_, 1, v___x_1934_);
    v___x_1938_ = l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__17;
    v___x_1939_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1939_, 0, v___x_1937_);
    leanh::lean_ctor_set(v___x_1939_, 1, v___x_1938_);
    v___x_1940_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1940_, 0, v___x_1935_);
    leanh::lean_ctor_set(v___x_1940_, 1, v___x_1939_);
    v___x_1941_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1941_, 0, v___x_1940_);
    leanh::lean_ctor_set_uint8(
        v___x_1941_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1910_,
    );
    return v___x_1941_;
}
pub unsafe fn l_Lean_Meta_Ext_instReprExtTheorem_repr(
    mut v_x_1942_: *mut leanh::LeanObject,
    mut v_prec_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg(v_x_1942_);
    return v___x_1944_;
}
pub unsafe fn l_Lean_Meta_Ext_instReprExtTheorem_repr___boxed(
    mut v_x_1945_: *mut leanh::LeanObject,
    mut v_prec_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_Lean_Meta_Ext_instReprExtTheorem_repr(v_x_1945_, v_prec_1946_);
    leanh::lean_dec(v_prec_1946_);
    return v_res_1947_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg(
    mut v_xs_1950_: *mut leanh::LeanObject,
    mut v_ys_1951_: *mut leanh::LeanObject,
    mut v_x_1952_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1954_: u8 = 0;
    let mut v_one_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1953_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1954_ = lean_nat_dec_eq(v_x_1952_, v_zero_1953_);
                if v_isZero_1954_ == 1 {
                    leanh::lean_dec(v_x_1952_);
                    return v_isZero_1954_;
                } else {
                    v_one_1955_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1956_ = lean_nat_sub(v_x_1952_, v_one_1955_);
                    leanh::lean_dec(v_x_1952_);
                    v___x_1957_ = lean_array_fget_borrowed(v_xs_1950_, v_n_1956_);
                    v___x_1958_ = lean_array_fget_borrowed(v_ys_1951_, v_n_1956_);
                    v___x_1959_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_1957_, v___x_1958_);
                    if v___x_1959_ == 0 {
                        leanh::lean_dec(v_n_1956_);
                        return v___x_1959_;
                    } else {
                        v_x_1952_ = v_n_1956_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg___boxed(
    mut v_xs_1961_: *mut leanh::LeanObject,
    mut v_ys_1962_: *mut leanh::LeanObject,
    mut v_x_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1964_: u8 = 0;
    let mut v_r_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg(
        v_xs_1961_, v_ys_1962_, v_x_1963_,
    );
    leanh::lean_dec_ref(v_ys_1962_);
    leanh::lean_dec_ref(v_xs_1961_);
    v_r_1965_ = leanh::lean_box((v_res_1964_) as usize);
    return v_r_1965_;
}
pub unsafe fn l_Lean_Meta_Ext_instBEqExtTheorem_beq(
    mut v_x_1966_: *mut leanh::LeanObject,
    mut v_x_1967_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_declName_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    v_declName_1968_ = leanh::lean_ctor_get(v_x_1966_, 0);
    v_priority_1969_ = leanh::lean_ctor_get(v_x_1966_, 1);
    v_keys_1970_ = leanh::lean_ctor_get(v_x_1966_, 2);
    v_declName_1971_ = leanh::lean_ctor_get(v_x_1967_, 0);
    v_priority_1972_ = leanh::lean_ctor_get(v_x_1967_, 1);
    v_keys_1973_ = leanh::lean_ctor_get(v_x_1967_, 2);
    v___x_1974_ = lean_name_eq(v_declName_1968_, v_declName_1971_);
    if v___x_1974_ == 0 {
        return v___x_1974_;
    } else {
        let mut v___x_1975_: u8 = 0;
        v___x_1975_ = lean_nat_dec_eq(v_priority_1969_, v_priority_1972_);
        if v___x_1975_ == 0 {
            return v___x_1975_;
        } else {
            let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1978_: u8 = 0;
            v___x_1976_ = lean_array_get_size(v_keys_1970_);
            v___x_1977_ = lean_array_get_size(v_keys_1973_);
            v___x_1978_ = lean_nat_dec_eq(v___x_1976_, v___x_1977_);
            if v___x_1978_ == 0 {
                return v___x_1978_;
            } else {
                let mut v___x_1979_: u8 = 0;
                v___x_1979_ =
                    l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg(
                        v_keys_1970_,
                        v_keys_1973_,
                        v___x_1976_,
                    );
                return v___x_1979_;
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Ext_instBEqExtTheorem_beq___boxed(
    mut v_x_1980_: *mut leanh::LeanObject,
    mut v_x_1981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1982_: u8 = 0;
    let mut v_r_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1982_ = l_Lean_Meta_Ext_instBEqExtTheorem_beq(v_x_1980_, v_x_1981_);
    leanh::lean_dec_ref(v_x_1981_);
    leanh::lean_dec_ref(v_x_1980_);
    v_r_1983_ = leanh::lean_box((v_res_1982_) as usize);
    return v_r_1983_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0(
    mut v_xs_1984_: *mut leanh::LeanObject,
    mut v_ys_1985_: *mut leanh::LeanObject,
    mut v_hsz_1986_: *mut leanh::LeanObject,
    mut v_x_1987_: *mut leanh::LeanObject,
    mut v_x_1988_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1989_: u8 = 0;
    v___x_1989_ = l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg(
        v_xs_1984_, v_ys_1985_, v_x_1987_,
    );
    return v___x_1989_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___boxed(
    mut v_xs_1990_: *mut leanh::LeanObject,
    mut v_ys_1991_: *mut leanh::LeanObject,
    mut v_hsz_1992_: *mut leanh::LeanObject,
    mut v_x_1993_: *mut leanh::LeanObject,
    mut v_x_1994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1995_: u8 = 0;
    let mut v_r_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1995_ = l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0(
        v_xs_1990_,
        v_ys_1991_,
        v_hsz_1992_,
        v_x_1993_,
        v_x_1994_,
    );
    leanh::lean_dec_ref(v_ys_1991_);
    leanh::lean_dec_ref(v_xs_1990_);
    v_r_1996_ = leanh::lean_box((v_res_1995_) as usize);
    return v_r_1996_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(
    mut v_as_1999_: *mut leanh::LeanObject,
    mut v_i_2000_: usize,
    mut v_stop_2001_: usize,
    mut v_b_2002_: u64,
) -> u64 {
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: u64 = 0;
    let mut v___x_2006_: u64 = 0;
    let mut v___x_2007_: usize = 0;
    let mut v___x_2008_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2003_ = lean_usize_dec_eq(v_i_2000_, v_stop_2001_);
                if v___x_2003_ == 0 {
                    v___x_2004_ = lean_array_uget_borrowed(v_as_1999_, v_i_2000_);
                    v___x_2005_ = l_Lean_Meta_DiscrTree_Key_hash(v___x_2004_);
                    v___x_2006_ = lean_uint64_mix_hash(v_b_2002_, v___x_2005_);
                    v___x_2007_ = 1usize;
                    v___x_2008_ = lean_usize_add(v_i_2000_, v___x_2007_);
                    v_i_2000_ = v___x_2008_;
                    v_b_2002_ = v___x_2006_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2002_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0___boxed(
    mut v_as_2010_: *mut leanh::LeanObject,
    mut v_i_2011_: *mut leanh::LeanObject,
    mut v_stop_2012_: *mut leanh::LeanObject,
    mut v_b_2013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2014_: usize = 0;
    let mut v_stop_boxed_2015_: usize = 0;
    let mut v_b_boxed_2016_: u64 = 0;
    let mut v_res_2017_: u64 = 0;
    let mut v_r_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2014_ = leanh::lean_unbox_usize(v_i_2011_);
    leanh::lean_dec(v_i_2011_);
    v_stop_boxed_2015_ = leanh::lean_unbox_usize(v_stop_2012_);
    leanh::lean_dec(v_stop_2012_);
    v_b_boxed_2016_ = leanh::lean_unbox_uint64(v_b_2013_);
    leanh::lean_dec_ref(v_b_2013_);
    v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(v_as_2010_, v_i_boxed_2014_, v_stop_boxed_2015_, v_b_boxed_2016_);
    leanh::lean_dec_ref(v_as_2010_);
    v_r_2018_ = leanh::lean_box_uint64(v_res_2017_);
    return v_r_2018_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0() -> u64 {
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: u64 = 0;
    v___x_2019_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2020_ = lean_uint64_of_nat(v___x_2019_);
    return v___x_2020_;
}
pub unsafe fn l_Lean_Meta_Ext_instHashableExtTheorem_hash(
    mut v_x_2021_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_declName_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u64 = 0;
    let mut v___y_2027_: u64 = 0;
    let mut v___x_2028_: u64 = 0;
    let mut v___x_2029_: u64 = 0;
    let mut v___x_2030_: u64 = 0;
    let mut v___x_2031_: u64 = 0;
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: u8 = 0;
    let mut v___x_2035_: u64 = 0;
    let mut v___x_2036_: u8 = 0;
    let mut v___x_2037_: u64 = 0;
    let mut v___x_2038_: usize = 0;
    let mut v___x_2039_: usize = 0;
    let mut v___x_2040_: u64 = 0;
    let mut v___x_2041_: u64 = 0;
    let mut v___x_2042_: usize = 0;
    let mut v___x_2043_: usize = 0;
    let mut v___x_2044_: u64 = 0;
    let mut v___x_2045_: u64 = 0;
    let mut v___x_2046_: u64 = 0;
    let mut v_hash_2047_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_2022_ = leanh::lean_ctor_get(v_x_2021_, 0);
                v_priority_2023_ = leanh::lean_ctor_get(v_x_2021_, 1);
                v_keys_2024_ = leanh::lean_ctor_get(v_x_2021_, 2);
                v___x_2025_ = 0u64;
                if leanh::lean_obj_tag(v_declName_2022_) == 0 {
                    v___x_2046_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once
                        ),
                        _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0,
                    );
                    v___y_2027_ = v___x_2046_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2047_ = leanh::lean_ctor_get_uint64(
                        v_declName_2022_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2027_ = v_hash_2047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2028_ = lean_uint64_mix_hash(v___x_2025_, v___y_2027_);
                v___x_2029_ = lean_uint64_of_nat(v_priority_2023_);
                v___x_2030_ = lean_uint64_mix_hash(v___x_2028_, v___x_2029_);
                v___x_2031_ = 7u64;
                v___x_2032_ = leanh::lean_unsigned_to_nat(0);
                v___x_2033_ = lean_array_get_size(v_keys_2024_);
                v___x_2034_ = lean_nat_dec_lt(v___x_2032_, v___x_2033_);
                if v___x_2034_ == 0 {
                    v___x_2035_ = lean_uint64_mix_hash(v___x_2030_, v___x_2031_);
                    return v___x_2035_;
                } else {
                    v___x_2036_ = lean_nat_dec_le(v___x_2033_, v___x_2033_);
                    if v___x_2036_ == 0 {
                        if v___x_2034_ == 0 {
                            v___x_2037_ = lean_uint64_mix_hash(v___x_2030_, v___x_2031_);
                            return v___x_2037_;
                        } else {
                            v___x_2038_ = 0usize;
                            v___x_2039_ = lean_usize_of_nat(v___x_2033_);
                            v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(v_keys_2024_, v___x_2038_, v___x_2039_, v___x_2031_);
                            v___x_2041_ = lean_uint64_mix_hash(v___x_2030_, v___x_2040_);
                            return v___x_2041_;
                        }
                    } else {
                        v___x_2042_ = 0usize;
                        v___x_2043_ = lean_usize_of_nat(v___x_2033_);
                        v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(v_keys_2024_, v___x_2042_, v___x_2043_, v___x_2031_);
                        v___x_2045_ = lean_uint64_mix_hash(v___x_2030_, v___x_2044_);
                        return v___x_2045_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Ext_instHashableExtTheorem_hash___boxed(
    mut v_x_2048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2049_: u64 = 0;
    let mut v_r_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2049_ = l_Lean_Meta_Ext_instHashableExtTheorem_hash(v_x_2048_);
    leanh::lean_dec_ref(v_x_2048_);
    v_r_2050_ = leanh::lean_box_uint64(v_res_2049_);
    return v_r_2050_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2053_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2054_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0);
    v___x_2055_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2055_, 0, v___x_2054_);
    return v___x_2055_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0(
    mut v_00_u03b2_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1);
    return v___x_2057_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2058_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2059_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0_once),
        _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0,
    );
    v___x_2060_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2060_, 0, v___x_2059_);
    return v___x_2060_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2061_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0(leanh::lean_box(0));
    return v___x_2061_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2062_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2_once),
        _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2,
    );
    v___x_2063_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1_once),
        _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1,
    );
    v___x_2064_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2064_, 0, v___x_2063_);
    leanh::lean_ctor_set(v___x_2064_, 1, v___x_2062_);
    return v___x_2064_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default()
-> *mut leanh::LeanObject {
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once),
        _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3,
    );
    return v___x_2065_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_instInhabitedExtTheorems() -> *mut leanh::LeanObject {
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2066_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
    return v___x_2066_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(
    mut v_x_2067_: *mut leanh::LeanObject,
    mut v_a_2068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2069_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2069_, 0, v_a_2068_);
    leanh::lean_inc_ref_n(v___x_2069_, 2);
    v___x_2070_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2070_, 0, v___x_2069_);
    leanh::lean_ctor_set(v___x_2070_, 1, v___x_2069_);
    leanh::lean_ctor_set(v___x_2070_, 2, v___x_2069_);
    return v___x_2070_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(
    mut v_x_2071_: *mut leanh::LeanObject,
    mut v_a_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2073_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v_x_2071_, v_a_2072_);
    leanh::lean_dec_ref(v_x_2071_);
    return v_res_2073_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16(
    mut v_xs_2074_: *mut leanh::LeanObject,
    mut v_v_2075_: *mut leanh::LeanObject,
    mut v_i_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2077_ = lean_array_get_size(v_xs_2074_);
                v___x_2078_ = lean_nat_dec_lt(v_i_2076_, v___x_2077_);
                if v___x_2078_ == 0 {
                    leanh::lean_dec(v_i_2076_);
                    v___x_2079_ = leanh::lean_box(0);
                    return v___x_2079_;
                } else {
                    v___x_2080_ = lean_array_fget_borrowed(v_xs_2074_, v_i_2076_);
                    v___x_2081_ = lean_name_eq(v___x_2080_, v_v_2075_);
                    if v___x_2081_ == 0 {
                        v___x_2082_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2083_ = lean_nat_add(v_i_2076_, v___x_2082_);
                        leanh::lean_dec(v_i_2076_);
                        v_i_2076_ = v___x_2083_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2085_, 0, v_i_2076_);
                        return v___x_2085_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16___boxed(
    mut v_xs_2086_: *mut leanh::LeanObject,
    mut v_v_2087_: *mut leanh::LeanObject,
    mut v_i_2088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2089_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16(v_xs_2086_, v_v_2087_, v_i_2088_);
    leanh::lean_dec(v_v_2087_);
    leanh::lean_dec_ref(v_xs_2086_);
    return v_res_2089_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10(
    mut v_xs_2090_: *mut leanh::LeanObject,
    mut v_v_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ = leanh::lean_unsigned_to_nat(0);
    v___x_2093_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16(v_xs_2090_, v_v_2091_, v___x_2092_);
    return v___x_2093_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10___boxed(
    mut v_xs_2094_: *mut leanh::LeanObject,
    mut v_v_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10(v_xs_2094_, v_v_2095_);
    leanh::lean_dec(v_v_2095_);
    leanh::lean_dec_ref(v_xs_2094_);
    return v_res_2096_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0()
-> usize {
    let mut v___x_2097_: usize = 0;
    let mut v___x_2098_: usize = 0;
    let mut v___x_2099_: usize = 0;
    v___x_2097_ = 5usize;
    v___x_2098_ = 1usize;
    v___x_2099_ = lean_usize_shift_left(v___x_2098_, v___x_2097_);
    return v___x_2099_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1()
-> usize {
    let mut v___x_2100_: usize = 0;
    let mut v___x_2101_: usize = 0;
    let mut v___x_2102_: usize = 0;
    v___x_2100_ = 1usize;
    v___x_2101_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0);
    v___x_2102_ = lean_usize_sub(v___x_2101_, v___x_2100_);
    return v___x_2102_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(
    mut v_x_2103_: *mut leanh::LeanObject,
    mut v_x_2104_: usize,
    mut v_x_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: usize = 0;
    let mut v___x_2109_: usize = 0;
    let mut v___x_2110_: usize = 0;
    let mut v_j_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: u8 = 0;
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2117_: u8 = 0;
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2122_: u8 = 0;
    let mut v_unused_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v_node_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v_entries_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: usize = 0;
    let mut v_newNode_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2147_: u8 = 0;
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut v_isSharedCheck_2156_: u8 = 0;
    let mut v_isSharedCheck_2157_: u8 = 0;
    let mut v_unused_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2103_) == 0 {
                    v_es_2106_ = leanh::lean_ctor_get(v_x_2103_, 0);
                    v___x_2107_ = leanh::lean_box(2);
                    v___x_2108_ = 5usize;
                    v___x_2109_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
                    v___x_2110_ = lean_usize_land(v_x_2104_, v___x_2109_);
                    v_j_2111_ = lean_usize_to_nat(v___x_2110_);
                    v_entry_2112_ = lean_array_get(v___x_2107_, v_es_2106_, v_j_2111_);
                    match leanh::lean_obj_tag(v_entry_2112_) {
                        0 => {
                            v_key_2113_ = leanh::lean_ctor_get(v_entry_2112_, 0);
                            leanh::lean_inc(v_key_2113_);
                            leanh::lean_dec_ref_known(v_entry_2112_, 2);
                            v___x_2114_ = lean_name_eq(v_x_2105_, v_key_2113_);
                            leanh::lean_dec(v_key_2113_);
                            if v___x_2114_ == 0 {
                                leanh::lean_dec(v_j_2111_);
                                return v_x_2103_;
                            } else {
                                leanh::lean_inc_ref(v_es_2106_);
                                v_isSharedCheck_2122_ =
                                    (!leanh::lean_is_exclusive(v_x_2103_)) as u8;
                                if v_isSharedCheck_2122_ == 0 {
                                    v_unused_2123_ = leanh::lean_ctor_get(v_x_2103_, 0);
                                    leanh::lean_dec(v_unused_2123_);
                                    v___x_2116_ = v_x_2103_;
                                    v_isShared_2117_ = v_isSharedCheck_2122_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_2103_);
                                    v___x_2116_ = leanh::lean_box(0);
                                    v_isShared_2117_ = v_isSharedCheck_2122_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            leanh::lean_inc_ref(v_es_2106_);
                            v_isSharedCheck_2157_ =
                                (!leanh::lean_is_exclusive(v_x_2103_)) as u8;
                            if v_isSharedCheck_2157_ == 0 {
                                v_unused_2158_ = leanh::lean_ctor_get(v_x_2103_, 0);
                                leanh::lean_dec(v_unused_2158_);
                                v___x_2125_ = v_x_2103_;
                                v_isShared_2126_ = v_isSharedCheck_2157_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_x_2103_);
                                v___x_2125_ = leanh::lean_box(0);
                                v_isShared_2126_ = v_isSharedCheck_2157_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_j_2111_);
                            return v_x_2103_;
                        }
                    }
                } else {
                    v_ks_2159_ = leanh::lean_ctor_get(v_x_2103_, 0);
                    v_vs_2160_ = leanh::lean_ctor_get(v_x_2103_, 1);
                    v_isSharedCheck_2174_ = (!leanh::lean_is_exclusive(v_x_2103_)) as u8;
                    if v_isSharedCheck_2174_ == 0 {
                        v___x_2162_ = v_x_2103_;
                        v_isShared_2163_ = v_isSharedCheck_2174_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2160_);
                        leanh::lean_inc(v_ks_2159_);
                        leanh::lean_dec(v_x_2103_);
                        v___x_2162_ = leanh::lean_box(0);
                        v_isShared_2163_ = v_isSharedCheck_2174_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2118_ = lean_array_set(v_es_2106_, v_j_2111_, v___x_2107_);
                leanh::lean_dec(v_j_2111_);
                if v_isShared_2117_ == 0 {
                    leanh::lean_ctor_set(v___x_2116_, 0, v___x_2118_);
                    v___x_2120_ = v___x_2116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2121_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
                    v___x_2120_ = v_reuseFailAlloc_2121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2120_;
            }
            3 => {
                v_node_2127_ = leanh::lean_ctor_get(v_entry_2112_, 0);
                v_isSharedCheck_2156_ = (!leanh::lean_is_exclusive(v_entry_2112_)) as u8;
                if v_isSharedCheck_2156_ == 0 {
                    v___x_2129_ = v_entry_2112_;
                    v_isShared_2130_ = v_isSharedCheck_2156_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_node_2127_);
                    leanh::lean_dec(v_entry_2112_);
                    v___x_2129_ = leanh::lean_box(0);
                    v_isShared_2130_ = v_isSharedCheck_2156_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_2131_ = lean_array_set(v_es_2106_, v_j_2111_, v___x_2107_);
                v___x_2132_ = lean_usize_shift_right(v_x_2104_, v___x_2108_);
                v_newNode_2133_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(v_node_2127_, v___x_2132_, v_x_2105_);
                leanh::lean_inc_ref(v_newNode_2133_);
                v___x_2134_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2133_);
                if leanh::lean_obj_tag(v___x_2134_) == 0 {
                    if v_isShared_2130_ == 0 {
                        leanh::lean_ctor_set(v___x_2129_, 0, v_newNode_2133_);
                        v___x_2136_ = v___x_2129_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2141_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_newNode_2133_);
                        v___x_2136_ = v_reuseFailAlloc_2141_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_newNode_2133_);
                    leanh::lean_del_object(v___x_2129_);
                    v_val_2142_ = leanh::lean_ctor_get(v___x_2134_, 0);
                    leanh::lean_inc(v_val_2142_);
                    leanh::lean_dec_ref_known(v___x_2134_, 1);
                    v_fst_2143_ = leanh::lean_ctor_get(v_val_2142_, 0);
                    v_snd_2144_ = leanh::lean_ctor_get(v_val_2142_, 1);
                    v_isSharedCheck_2155_ = (!leanh::lean_is_exclusive(v_val_2142_)) as u8;
                    if v_isSharedCheck_2155_ == 0 {
                        v___x_2146_ = v_val_2142_;
                        v_isShared_2147_ = v_isSharedCheck_2155_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2144_);
                        leanh::lean_inc(v_fst_2143_);
                        leanh::lean_dec(v_val_2142_);
                        v___x_2146_ = leanh::lean_box(0);
                        v_isShared_2147_ = v_isSharedCheck_2155_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2137_ = lean_array_set(v_entries_2131_, v_j_2111_, v___x_2136_);
                leanh::lean_dec(v_j_2111_);
                if v_isShared_2126_ == 0 {
                    leanh::lean_ctor_set(v___x_2125_, 0, v___x_2137_);
                    v___x_2139_ = v___x_2125_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2140_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
                    v___x_2139_ = v_reuseFailAlloc_2140_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2139_;
            }
            7 => {
                if v_isShared_2147_ == 0 {
                    v___x_2149_ = v___x_2146_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_fst_2143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_snd_2144_);
                    v___x_2149_ = v_reuseFailAlloc_2154_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2150_ = lean_array_set(v_entries_2131_, v_j_2111_, v___x_2149_);
                leanh::lean_dec(v_j_2111_);
                if v_isShared_2126_ == 0 {
                    leanh::lean_ctor_set(v___x_2125_, 0, v___x_2150_);
                    v___x_2152_ = v___x_2125_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2153_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
                    v___x_2152_ = v_reuseFailAlloc_2153_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2152_;
            }
            10 => {
                v___x_2164_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10(v_ks_2159_, v_x_2105_);
                if leanh::lean_obj_tag(v___x_2164_) == 0 {
                    if v_isShared_2163_ == 0 {
                        v___x_2166_ = v___x_2162_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2167_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_ks_2159_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_vs_2160_);
                        v___x_2166_ = v_reuseFailAlloc_2167_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_val_2168_ = leanh::lean_ctor_get(v___x_2164_, 0);
                    leanh::lean_inc_n(v_val_2168_, 2);
                    leanh::lean_dec_ref_known(v___x_2164_, 1);
                    v_keys_x27_2169_ = l_Array_eraseIdx___redArg(v_ks_2159_, v_val_2168_);
                    v_vals_x27_2170_ = l_Array_eraseIdx___redArg(v_vs_2160_, v_val_2168_);
                    if v_isShared_2163_ == 0 {
                        leanh::lean_ctor_set(v___x_2162_, 1, v_vals_x27_2170_);
                        leanh::lean_ctor_set(v___x_2162_, 0, v_keys_x27_2169_);
                        v___x_2172_ = v___x_2162_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2173_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_keys_x27_2169_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_vals_x27_2170_);
                        v___x_2172_ = v_reuseFailAlloc_2173_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_2166_;
            }
            12 => {
                return v___x_2172_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(
    mut v_x_2175_: *mut leanh::LeanObject,
    mut v_x_2176_: *mut leanh::LeanObject,
    mut v_x_2177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1770__boxed_2178_: usize = 0;
    let mut v_res_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1770__boxed_2178_ = leanh::lean_unbox_usize(v_x_2176_);
    leanh::lean_dec(v_x_2176_);
    v_res_2179_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(v_x_2175_, v_x_1770__boxed_2178_, v_x_2177_);
    leanh::lean_dec(v_x_2177_);
    return v_res_2179_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_2180_: *mut leanh::LeanObject,
    mut v_x_2181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2183_: u64 = 0;
    let mut v_h_2184_: usize = 0;
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u64 = 0;
    let mut v_hash_2187_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2181_) == 0 {
                    v___x_2186_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once
                        ),
                        _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0,
                    );
                    v___y_2183_ = v___x_2186_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2187_ = leanh::lean_ctor_get_uint64(
                        v_x_2181_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2183_ = v_hash_2187_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_h_2184_ = lean_uint64_to_usize(v___y_2183_);
                v___x_2185_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(v_x_2180_, v_h_2184_, v_x_2181_);
                return v___x_2185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_x_2188_: *mut leanh::LeanObject,
    mut v_x_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2190_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_2188_, v_x_2189_);
    leanh::lean_dec(v_x_2189_);
    return v_res_2190_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_keys_2191_: *mut leanh::LeanObject,
    mut v_vals_2192_: *mut leanh::LeanObject,
    mut v_i_2193_: *mut leanh::LeanObject,
    mut v_k_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u8 = 0;
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u8 = 0;
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2195_ = lean_array_get_size(v_keys_2191_);
                v___x_2196_ = lean_nat_dec_lt(v_i_2193_, v___x_2195_);
                if v___x_2196_ == 0 {
                    leanh::lean_dec(v_i_2193_);
                    v___x_2197_ = leanh::lean_box(0);
                    return v___x_2197_;
                } else {
                    v_k_x27_2198_ = lean_array_fget_borrowed(v_keys_2191_, v_i_2193_);
                    v___x_2199_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_2194_, v_k_x27_2198_);
                    if v___x_2199_ == 0 {
                        v___x_2200_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2201_ = lean_nat_add(v_i_2193_, v___x_2200_);
                        leanh::lean_dec(v_i_2193_);
                        v_i_2193_ = v___x_2201_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2203_ = lean_array_fget_borrowed(v_vals_2192_, v_i_2193_);
                        leanh::lean_dec(v_i_2193_);
                        leanh::lean_inc(v___x_2203_);
                        v___x_2204_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2204_, 0, v___x_2203_);
                        return v___x_2204_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_keys_2205_: *mut leanh::LeanObject,
    mut v_vals_2206_: *mut leanh::LeanObject,
    mut v_i_2207_: *mut leanh::LeanObject,
    mut v_k_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2209_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_keys_2205_, v_vals_2206_, v_i_2207_, v_k_2208_);
    leanh::lean_dec(v_k_2208_);
    leanh::lean_dec_ref(v_vals_2206_);
    leanh::lean_dec_ref(v_keys_2205_);
    return v_res_2209_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_2210_: *mut leanh::LeanObject,
    mut v_x_2211_: usize,
    mut v_x_2212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: usize = 0;
    let mut v___x_2216_: usize = 0;
    let mut v___x_2217_: usize = 0;
    let mut v_j_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: usize = 0;
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2210_) == 0 {
                    v_es_2213_ = leanh::lean_ctor_get(v_x_2210_, 0);
                    v___x_2214_ = leanh::lean_box(2);
                    v___x_2215_ = 5usize;
                    v___x_2216_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
                    v___x_2217_ = lean_usize_land(v_x_2211_, v___x_2216_);
                    v_j_2218_ = lean_usize_to_nat(v___x_2217_);
                    v___x_2219_ = lean_array_get_borrowed(v___x_2214_, v_es_2213_, v_j_2218_);
                    leanh::lean_dec(v_j_2218_);
                    match leanh::lean_obj_tag(v___x_2219_) {
                        0 => {
                            v_key_2220_ = leanh::lean_ctor_get(v___x_2219_, 0);
                            v_val_2221_ = leanh::lean_ctor_get(v___x_2219_, 1);
                            v___x_2222_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2212_, v_key_2220_);
                            if v___x_2222_ == 0 {
                                v___x_2223_ = leanh::lean_box(0);
                                return v___x_2223_;
                            } else {
                                leanh::lean_inc(v_val_2221_);
                                v___x_2224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2224_, 0, v_val_2221_);
                                return v___x_2224_;
                            }
                        }
                        1 => {
                            v_node_2225_ = leanh::lean_ctor_get(v___x_2219_, 0);
                            v___x_2226_ = lean_usize_shift_right(v_x_2211_, v___x_2215_);
                            v_x_2210_ = v_node_2225_;
                            v_x_2211_ = v___x_2226_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2228_ = leanh::lean_box(0);
                            return v___x_2228_;
                        }
                    }
                } else {
                    v_ks_2229_ = leanh::lean_ctor_get(v_x_2210_, 0);
                    v_vs_2230_ = leanh::lean_ctor_get(v_x_2210_, 1);
                    v___x_2231_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2232_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_ks_2229_, v_vs_2230_, v___x_2231_, v_x_2212_);
                    return v___x_2232_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2233_: *mut leanh::LeanObject,
    mut v_x_2234_: *mut leanh::LeanObject,
    mut v_x_2235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1953__boxed_2236_: usize = 0;
    let mut v_res_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1953__boxed_2236_ = leanh::lean_unbox_usize(v_x_2234_);
    leanh::lean_dec(v_x_2234_);
    v_res_2237_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2233_, v_x_1953__boxed_2236_, v_x_2235_);
    leanh::lean_dec(v_x_2235_);
    leanh::lean_dec_ref(v_x_2233_);
    return v_res_2237_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_2238_: *mut leanh::LeanObject,
    mut v_x_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2240_: u64 = 0;
    let mut v___x_2241_: usize = 0;
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_2239_);
    v___x_2241_ = lean_uint64_to_usize(v___x_2240_);
    v___x_2242_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2238_, v___x_2241_, v_x_2239_);
    return v___x_2242_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_x_2243_: *mut leanh::LeanObject,
    mut v_x_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2245_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2243_, v_x_2244_);
    leanh::lean_dec(v_x_2244_);
    leanh::lean_dec_ref(v_x_2243_);
    return v_res_2245_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__11(
    mut v_vs_2246_: *mut leanh::LeanObject,
    mut v_v_2247_: *mut leanh::LeanObject,
    mut v_i_2248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: u8 = 0;
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: u8 = 0;
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2249_ = lean_array_get_size(v_vs_2246_);
                v___x_2250_ = lean_nat_dec_lt(v_i_2248_, v___x_2249_);
                if v___x_2250_ == 0 {
                    leanh::lean_dec(v_i_2248_);
                    v___x_2251_ = lean_array_push(v_vs_2246_, v_v_2247_);
                    return v___x_2251_;
                } else {
                    v___x_2252_ = lean_array_fget_borrowed(v_vs_2246_, v_i_2248_);
                    v___x_2253_ = l_Lean_Meta_Ext_instBEqExtTheorem_beq(v_v_2247_, v___x_2252_);
                    if v___x_2253_ == 0 {
                        v___x_2254_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2255_ = lean_nat_add(v_i_2248_, v___x_2254_);
                        leanh::lean_dec(v_i_2248_);
                        v_i_2248_ = v___x_2255_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2257_ = lean_array_fset(v_vs_2246_, v_i_2248_, v_v_2247_);
                        leanh::lean_dec(v_i_2248_);
                        return v___x_2257_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5(
    mut v_vs_2258_: *mut leanh::LeanObject,
    mut v_v_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = leanh::lean_unsigned_to_nat(0);
    v___x_2261_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__11(v_vs_2258_, v_v_2259_, v___x_2260_);
    return v___x_2261_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(
    mut v_x_2262_: *mut leanh::LeanObject,
    mut v_keys_2263_: *mut leanh::LeanObject,
    mut v_v_2264_: *mut leanh::LeanObject,
    mut v_k_2265_: *mut leanh::LeanObject,
    mut v_x_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = leanh::lean_unsigned_to_nat(1);
    v___x_2268_ = lean_nat_add(v_x_2262_, v___x_2267_);
    v_c_2269_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        leanh::lean_box(0),
        v_keys_2263_,
        v_v_2264_,
        v___x_2268_,
    );
    leanh::lean_dec(v___x_2268_);
    v___x_2270_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2270_, 0, v_k_2265_);
    leanh::lean_ctor_set(v___x_2270_, 1, v_c_2269_);
    return v___x_2270_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0___boxed(
    mut v_x_2271_: *mut leanh::LeanObject,
    mut v_keys_2272_: *mut leanh::LeanObject,
    mut v_v_2273_: *mut leanh::LeanObject,
    mut v_k_2274_: *mut leanh::LeanObject,
    mut v_x_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_2271_, v_keys_2272_, v_v_2273_, v_k_2274_, v_x_2275_);
    leanh::lean_dec_ref(v_keys_2272_);
    leanh::lean_dec(v_x_2271_);
    return v_res_2276_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(
    mut v_a_2277_: *mut leanh::LeanObject,
    mut v_b_2278_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: u8 = 0;
    v_fst_2279_ = leanh::lean_ctor_get(v_a_2277_, 0);
    v_fst_2280_ = leanh::lean_ctor_get(v_b_2278_, 0);
    v___x_2281_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_2279_, v_fst_2280_);
    return v___x_2281_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1___boxed(
    mut v_a_2282_: *mut leanh::LeanObject,
    mut v_b_2283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2284_: u8 = 0;
    let mut v_r_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2284_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_a_2282_, v_b_2283_);
    leanh::lean_dec_ref(v_b_2283_);
    leanh::lean_dec_ref(v_a_2282_);
    v_r_2285_ = leanh::lean_box((v_res_2284_) as usize);
    return v_r_2285_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg(
    mut v_x_2290_: *mut leanh::LeanObject,
    mut v_keys_2291_: *mut leanh::LeanObject,
    mut v_v_2292_: *mut leanh::LeanObject,
    mut v_k_2293_: *mut leanh::LeanObject,
    mut v_as_2294_: *mut leanh::LeanObject,
    mut v_k_2295_: *mut leanh::LeanObject,
    mut v_x_2296_: *mut leanh::LeanObject,
    mut v_x_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_midVal_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    let mut v_snd_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2318_: u8 = 0;
    let mut v_unused_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2298_ = lean_nat_add(v_x_2296_, v_x_2297_);
                v___x_2299_ = leanh::lean_unsigned_to_nat(1);
                v_mid_2300_ = lean_nat_shiftr(v___x_2298_, v___x_2299_);
                leanh::lean_dec(v___x_2298_);
                v_midVal_2301_ = lean_array_fget(v_as_2294_, v_mid_2300_);
                v___x_2302_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_midVal_2301_, v_k_2295_);
                if v___x_2302_ == 0 {
                    leanh::lean_dec(v_x_2297_);
                    v___x_2303_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_2295_, v_midVal_2301_);
                    if v___x_2303_ == 0 {
                        leanh::lean_dec(v_x_2296_);
                        v___x_2304_ = lean_array_get_size(v_as_2294_);
                        v___x_2305_ = lean_nat_dec_lt(v_mid_2300_, v___x_2304_);
                        if v___x_2305_ == 0 {
                            leanh::lean_dec(v_midVal_2301_);
                            leanh::lean_dec(v_mid_2300_);
                            leanh::lean_dec(v_k_2293_);
                            leanh::lean_dec_ref(v_v_2292_);
                            return v_as_2294_;
                        } else {
                            v_snd_2306_ = leanh::lean_ctor_get(v_midVal_2301_, 1);
                            v_isSharedCheck_2318_ =
                                (!leanh::lean_is_exclusive(v_midVal_2301_)) as u8;
                            if v_isSharedCheck_2318_ == 0 {
                                v_unused_2319_ = leanh::lean_ctor_get(v_midVal_2301_, 0);
                                leanh::lean_dec(v_unused_2319_);
                                v___x_2308_ = v_midVal_2301_;
                                v_isShared_2309_ = v_isSharedCheck_2318_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_2306_);
                                leanh::lean_dec(v_midVal_2301_);
                                v___x_2308_ = leanh::lean_box(0);
                                v_isShared_2309_ = v_isSharedCheck_2318_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_midVal_2301_);
                        v_x_2297_ = v_mid_2300_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_midVal_2301_);
                    v___x_2321_ = lean_nat_dec_eq(v_mid_2300_, v_x_2296_);
                    if v___x_2321_ == 0 {
                        leanh::lean_dec(v_x_2296_);
                        v_x_2296_ = v_mid_2300_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_mid_2300_);
                        leanh::lean_dec(v_x_2297_);
                        v___x_2323_ = lean_nat_add(v_x_2290_, v___x_2299_);
                        v_c_2324_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(leanh::lean_box(0), v_keys_2291_, v_v_2292_, v___x_2323_);
                        leanh::lean_dec(v___x_2323_);
                        v___x_2325_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2325_, 0, v_k_2293_);
                        leanh::lean_ctor_set(v___x_2325_, 1, v_c_2324_);
                        v___x_2326_ = lean_nat_add(v_x_2296_, v___x_2299_);
                        leanh::lean_dec(v_x_2296_);
                        v_j_2327_ = lean_array_get_size(v_as_2294_);
                        v_as_2328_ = lean_array_push(v_as_2294_, v___x_2325_);
                        v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            leanh::lean_box(0),
                            v___x_2326_,
                            v_as_2328_,
                            v_j_2327_,
                        );
                        leanh::lean_dec(v___x_2326_);
                        return v___x_2329_;
                    }
                }
            }
            1 => {
                v___x_2310_ = leanh::lean_box(0);
                v_xs_x27_2311_ = lean_array_fset(v_as_2294_, v_mid_2300_, v___x_2310_);
                v___x_2312_ = lean_nat_add(v_x_2290_, v___x_2299_);
                v_c_2313_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v_keys_2291_, v_v_2292_, v___x_2312_, v_snd_2306_);
                leanh::lean_dec(v___x_2312_);
                if v_isShared_2309_ == 0 {
                    leanh::lean_ctor_set(v___x_2308_, 1, v_c_2313_);
                    leanh::lean_ctor_set(v___x_2308_, 0, v_k_2293_);
                    v___x_2315_ = v___x_2308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2317_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_k_2293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_c_2313_);
                    v___x_2315_ = v_reuseFailAlloc_2317_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2316_ = lean_array_fset(v_xs_x27_2311_, v_mid_2300_, v___x_2315_);
                leanh::lean_dec(v_mid_2300_);
                return v___x_2316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6(
    mut v_x_2330_: *mut leanh::LeanObject,
    mut v_keys_2331_: *mut leanh::LeanObject,
    mut v_v_2332_: *mut leanh::LeanObject,
    mut v_k_2333_: *mut leanh::LeanObject,
    mut v_as_2334_: *mut leanh::LeanObject,
    mut v_k_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    v___x_2336_ = lean_array_get_size(v_as_2334_);
    v___x_2337_ = leanh::lean_unsigned_to_nat(0);
    v___x_2338_ = lean_nat_dec_eq(v___x_2336_, v___x_2337_);
    if v___x_2338_ == 0 {
        let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: u8 = 0;
        v___x_2339_ = lean_array_fget_borrowed(v_as_2334_, v___x_2337_);
        v___x_2340_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_2335_, v___x_2339_);
        if v___x_2340_ == 0 {
            let mut v___x_2341_: u8 = 0;
            v___x_2341_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_2339_, v_k_2335_);
            if v___x_2341_ == 0 {
                let mut v___x_2342_: u8 = 0;
                v___x_2342_ = lean_nat_dec_lt(v___x_2337_, v___x_2336_);
                if v___x_2342_ == 0 {
                    leanh::lean_dec(v_k_2333_);
                    leanh::lean_dec_ref(v_v_2332_);
                    return v_as_2334_;
                } else {
                    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_inc(v___x_2339_);
                    v___x_2343_ = leanh::lean_box(0);
                    v_xs_x27_2344_ = lean_array_fset(v_as_2334_, v___x_2337_, v___x_2343_);
                    v___x_2345_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_2330_, v_keys_2331_, v_v_2332_, v_k_2333_, v___x_2339_);
                    v___x_2346_ = lean_array_fset(v_xs_x27_2344_, v___x_2337_, v___x_2345_);
                    return v___x_2346_;
                }
            } else {
                let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2350_: u8 = 0;
                v___x_2347_ = leanh::lean_unsigned_to_nat(1);
                v___x_2348_ = lean_nat_sub(v___x_2336_, v___x_2347_);
                v___x_2349_ = lean_array_fget_borrowed(v_as_2334_, v___x_2348_);
                v___x_2350_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_2349_, v_k_2335_);
                if v___x_2350_ == 0 {
                    let mut v___x_2351_: u8 = 0;
                    v___x_2351_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_2335_, v___x_2349_);
                    if v___x_2351_ == 0 {
                        let mut v___x_2352_: u8 = 0;
                        v___x_2352_ = lean_nat_dec_lt(v___x_2348_, v___x_2336_);
                        if v___x_2352_ == 0 {
                            leanh::lean_dec(v___x_2348_);
                            leanh::lean_dec(v_k_2333_);
                            leanh::lean_dec_ref(v_v_2332_);
                            return v_as_2334_;
                        } else {
                            let mut v___x_2353_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_xs_x27_2354_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2355_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2356_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_inc(v___x_2349_);
                            v___x_2353_ = leanh::lean_box(0);
                            v_xs_x27_2354_ = lean_array_fset(v_as_2334_, v___x_2348_, v___x_2353_);
                            v___x_2355_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_2330_, v_keys_2331_, v_v_2332_, v_k_2333_, v___x_2349_);
                            v___x_2356_ = lean_array_fset(v_xs_x27_2354_, v___x_2348_, v___x_2355_);
                            leanh::lean_dec(v___x_2348_);
                            return v___x_2356_;
                        }
                    } else {
                        let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_2357_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg(v_x_2330_, v_keys_2331_, v_v_2332_, v_k_2333_, v_as_2334_, v_k_2335_, v___x_2337_, v___x_2348_);
                        return v___x_2357_;
                    }
                } else {
                    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_2348_);
                    v___x_2358_ = leanh::lean_box(0);
                    v___x_2359_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_2330_, v_keys_2331_, v_v_2332_, v_k_2333_, v___x_2358_);
                    v___x_2360_ = lean_array_push(v_as_2334_, v___x_2359_);
                    return v___x_2360_;
                }
            }
        } else {
            let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_as_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2361_ = leanh::lean_box(0);
            v___x_2362_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_2330_, v_keys_2331_, v_v_2332_, v_k_2333_, v___x_2361_);
            v_as_2363_ = lean_array_push(v_as_2334_, v___x_2362_);
            v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                leanh::lean_box(0),
                v___x_2337_,
                v_as_2363_,
                v___x_2336_,
            );
            return v___x_2364_;
        }
    } else {
        let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2365_ = leanh::lean_box(0);
        v___x_2366_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_2330_, v_keys_2331_, v_v_2332_, v_k_2333_, v___x_2365_);
        v___x_2367_ = lean_array_push(v_as_2334_, v___x_2366_);
        return v___x_2367_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(
    mut v_keys_2368_: *mut leanh::LeanObject,
    mut v_v_2369_: *mut leanh::LeanObject,
    mut v_x_2370_: *mut leanh::LeanObject,
    mut v_x_2371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vs_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_2372_ = leanh::lean_ctor_get(v_x_2371_, 0);
                v_children_2373_ = leanh::lean_ctor_get(v_x_2371_, 1);
                v_isSharedCheck_2390_ = (!leanh::lean_is_exclusive(v_x_2371_)) as u8;
                if v_isSharedCheck_2390_ == 0 {
                    v___x_2375_ = v_x_2371_;
                    v_isShared_2376_ = v_isSharedCheck_2390_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_children_2373_);
                    leanh::lean_inc(v_vs_2372_);
                    leanh::lean_dec(v_x_2371_);
                    v___x_2375_ = leanh::lean_box(0);
                    v_isShared_2376_ = v_isSharedCheck_2390_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2377_ = lean_array_get_size(v_keys_2368_);
                v___x_2378_ = lean_nat_dec_lt(v_x_2370_, v___x_2377_);
                if v___x_2378_ == 0 {
                    v___x_2379_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_vs_2372_, v_v_2369_);
                    if v_isShared_2376_ == 0 {
                        leanh::lean_ctor_set(v___x_2375_, 0, v___x_2379_);
                        v___x_2381_ = v___x_2375_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2382_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2379_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_children_2373_);
                        v___x_2381_ = v_reuseFailAlloc_2382_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_2383_ = lean_array_fget_borrowed(v_keys_2368_, v_x_2370_);
                    v___x_2384_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__1;
                    leanh::lean_inc_n(v_k_2383_, 2);
                    v___x_2385_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2385_, 0, v_k_2383_);
                    leanh::lean_ctor_set(v___x_2385_, 1, v___x_2384_);
                    v_c_2386_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_2370_, v_keys_2368_, v_v_2369_, v_k_2383_, v_children_2373_, v___x_2385_);
                    leanh::lean_dec_ref_known(v___x_2385_, 2);
                    if v_isShared_2376_ == 0 {
                        leanh::lean_ctor_set(v___x_2375_, 1, v_c_2386_);
                        v___x_2388_ = v___x_2375_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2389_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_vs_2372_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_c_2386_);
                        v___x_2388_ = v_reuseFailAlloc_2389_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2381_;
            }
            3 => {
                return v___x_2388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(
    mut v_x_2391_: *mut leanh::LeanObject,
    mut v_keys_2392_: *mut leanh::LeanObject,
    mut v_v_2393_: *mut leanh::LeanObject,
    mut v_k_2394_: *mut leanh::LeanObject,
    mut v_x_2395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut v_unused_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2396_ = leanh::lean_ctor_get(v_x_2395_, 1);
                v_isSharedCheck_2406_ = (!leanh::lean_is_exclusive(v_x_2395_)) as u8;
                if v_isSharedCheck_2406_ == 0 {
                    v_unused_2407_ = leanh::lean_ctor_get(v_x_2395_, 0);
                    leanh::lean_dec(v_unused_2407_);
                    v___x_2398_ = v_x_2395_;
                    v_isShared_2399_ = v_isSharedCheck_2406_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2396_);
                    leanh::lean_dec(v_x_2395_);
                    v___x_2398_ = leanh::lean_box(0);
                    v_isShared_2399_ = v_isSharedCheck_2406_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2400_ = leanh::lean_unsigned_to_nat(1);
                v___x_2401_ = lean_nat_add(v_x_2391_, v___x_2400_);
                v_c_2402_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v_keys_2392_, v_v_2393_, v___x_2401_, v_snd_2396_);
                leanh::lean_dec(v___x_2401_);
                if v_isShared_2399_ == 0 {
                    leanh::lean_ctor_set(v___x_2398_, 1, v_c_2402_);
                    leanh::lean_ctor_set(v___x_2398_, 0, v_k_2394_);
                    v___x_2404_ = v___x_2398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2405_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_k_2394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_c_2402_);
                    v___x_2404_ = v_reuseFailAlloc_2405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2___boxed(
    mut v_x_2408_: *mut leanh::LeanObject,
    mut v_keys_2409_: *mut leanh::LeanObject,
    mut v_v_2410_: *mut leanh::LeanObject,
    mut v_k_2411_: *mut leanh::LeanObject,
    mut v_x_2412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_2408_, v_keys_2409_, v_v_2410_, v_k_2411_, v_x_2412_);
    leanh::lean_dec_ref(v_keys_2409_);
    leanh::lean_dec(v_x_2408_);
    return v_res_2413_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___boxed(
    mut v_keys_2414_: *mut leanh::LeanObject,
    mut v_v_2415_: *mut leanh::LeanObject,
    mut v_x_2416_: *mut leanh::LeanObject,
    mut v_x_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v_keys_2414_, v_v_2415_, v_x_2416_, v_x_2417_);
    leanh::lean_dec(v_x_2416_);
    leanh::lean_dec_ref(v_keys_2414_);
    return v_res_2418_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg___boxed(
    mut v_x_2419_: *mut leanh::LeanObject,
    mut v_keys_2420_: *mut leanh::LeanObject,
    mut v_v_2421_: *mut leanh::LeanObject,
    mut v_k_2422_: *mut leanh::LeanObject,
    mut v_as_2423_: *mut leanh::LeanObject,
    mut v_k_2424_: *mut leanh::LeanObject,
    mut v_x_2425_: *mut leanh::LeanObject,
    mut v_x_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2427_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg(v_x_2419_, v_keys_2420_, v_v_2421_, v_k_2422_, v_as_2423_, v_k_2424_, v_x_2425_, v_x_2426_);
    leanh::lean_dec_ref(v_k_2424_);
    leanh::lean_dec_ref(v_keys_2420_);
    leanh::lean_dec(v_x_2419_);
    return v_res_2427_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___boxed(
    mut v_x_2428_: *mut leanh::LeanObject,
    mut v_keys_2429_: *mut leanh::LeanObject,
    mut v_v_2430_: *mut leanh::LeanObject,
    mut v_k_2431_: *mut leanh::LeanObject,
    mut v_as_2432_: *mut leanh::LeanObject,
    mut v_k_2433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2434_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_2428_, v_keys_2429_, v_v_2430_, v_k_2431_, v_as_2432_, v_k_2433_);
    leanh::lean_dec_ref(v_k_2433_);
    leanh::lean_dec_ref(v_keys_2429_);
    leanh::lean_dec(v_x_2428_);
    return v_res_2434_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10___redArg(
    mut v_x_2435_: *mut leanh::LeanObject,
    mut v_x_2436_: *mut leanh::LeanObject,
    mut v_x_2437_: *mut leanh::LeanObject,
    mut v_x_2438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: u8 = 0;
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2439_ = leanh::lean_ctor_get(v_x_2435_, 0);
                v_vs_2440_ = leanh::lean_ctor_get(v_x_2435_, 1);
                v_isSharedCheck_2464_ = (!leanh::lean_is_exclusive(v_x_2435_)) as u8;
                if v_isSharedCheck_2464_ == 0 {
                    v___x_2442_ = v_x_2435_;
                    v_isShared_2443_ = v_isSharedCheck_2464_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2440_);
                    leanh::lean_inc(v_ks_2439_);
                    leanh::lean_dec(v_x_2435_);
                    v___x_2442_ = leanh::lean_box(0);
                    v_isShared_2443_ = v_isSharedCheck_2464_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2444_ = lean_array_get_size(v_ks_2439_);
                v___x_2445_ = lean_nat_dec_lt(v_x_2436_, v___x_2444_);
                if v___x_2445_ == 0 {
                    leanh::lean_dec(v_x_2436_);
                    v___x_2446_ = lean_array_push(v_ks_2439_, v_x_2437_);
                    v___x_2447_ = lean_array_push(v_vs_2440_, v_x_2438_);
                    if v_isShared_2443_ == 0 {
                        leanh::lean_ctor_set(v___x_2442_, 1, v___x_2447_);
                        leanh::lean_ctor_set(v___x_2442_, 0, v___x_2446_);
                        v___x_2449_ = v___x_2442_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2450_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2446_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 1, v___x_2447_);
                        v___x_2449_ = v_reuseFailAlloc_2450_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2451_ = lean_array_fget_borrowed(v_ks_2439_, v_x_2436_);
                    v___x_2452_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2437_, v_k_x27_2451_);
                    if v___x_2452_ == 0 {
                        if v_isShared_2443_ == 0 {
                            v___x_2454_ = v___x_2442_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2458_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_ks_2439_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_vs_2440_);
                            v___x_2454_ = v_reuseFailAlloc_2458_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2459_ = lean_array_fset(v_ks_2439_, v_x_2436_, v_x_2437_);
                        v___x_2460_ = lean_array_fset(v_vs_2440_, v_x_2436_, v_x_2438_);
                        leanh::lean_dec(v_x_2436_);
                        if v_isShared_2443_ == 0 {
                            leanh::lean_ctor_set(v___x_2442_, 1, v___x_2460_);
                            leanh::lean_ctor_set(v___x_2442_, 0, v___x_2459_);
                            v___x_2462_ = v___x_2442_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2463_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2459_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 1, v___x_2460_);
                            v___x_2462_ = v_reuseFailAlloc_2463_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2449_;
            }
            3 => {
                v___x_2455_ = leanh::lean_unsigned_to_nat(1);
                v___x_2456_ = lean_nat_add(v_x_2436_, v___x_2455_);
                leanh::lean_dec(v_x_2436_);
                v_x_2435_ = v___x_2454_;
                v_x_2436_ = v___x_2456_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_n_2465_: *mut leanh::LeanObject,
    mut v_k_2466_: *mut leanh::LeanObject,
    mut v_v_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = leanh::lean_unsigned_to_nat(0);
    v___x_2469_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_n_2465_, v___x_2468_, v_k_2466_, v_v_2467_);
    return v___x_2469_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2470_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(
    mut v_x_2471_: *mut leanh::LeanObject,
    mut v_x_2472_: usize,
    mut v_x_2473_: usize,
    mut v_x_2474_: *mut leanh::LeanObject,
    mut v_x_2475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: usize = 0;
    let mut v___x_2478_: usize = 0;
    let mut v___x_2479_: usize = 0;
    let mut v___x_2480_: usize = 0;
    let mut v_j_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: u8 = 0;
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v_v_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v___x_2501_: u8 = 0;
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut v_node_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v___x_2512_: usize = 0;
    let mut v___x_2513_: usize = 0;
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2518_: u8 = 0;
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2520_: u8 = 0;
    let mut v_unused_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2531_: u8 = 0;
    let mut v_ks_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: usize = 0;
    let mut v___x_2538_: u8 = 0;
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v_reuseFailAlloc_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2471_) == 0 {
                    v_es_2476_ = leanh::lean_ctor_get(v_x_2471_, 0);
                    v___x_2477_ = 5usize;
                    v___x_2478_ = 1usize;
                    v___x_2479_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
                    v___x_2480_ = lean_usize_land(v_x_2472_, v___x_2479_);
                    v_j_2481_ = lean_usize_to_nat(v___x_2480_);
                    v___x_2482_ = lean_array_get_size(v_es_2476_);
                    v___x_2483_ = lean_nat_dec_lt(v_j_2481_, v___x_2482_);
                    if v___x_2483_ == 0 {
                        leanh::lean_dec(v_j_2481_);
                        leanh::lean_dec(v_x_2475_);
                        leanh::lean_dec(v_x_2474_);
                        return v_x_2471_;
                    } else {
                        leanh::lean_inc_ref(v_es_2476_);
                        v_isSharedCheck_2520_ = (!leanh::lean_is_exclusive(v_x_2471_)) as u8;
                        if v_isSharedCheck_2520_ == 0 {
                            v_unused_2521_ = leanh::lean_ctor_get(v_x_2471_, 0);
                            leanh::lean_dec(v_unused_2521_);
                            v___x_2485_ = v_x_2471_;
                            v_isShared_2486_ = v_isSharedCheck_2520_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2471_);
                            v___x_2485_ = leanh::lean_box(0);
                            v_isShared_2486_ = v_isSharedCheck_2520_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2522_ = leanh::lean_ctor_get(v_x_2471_, 0);
                    v_vs_2523_ = leanh::lean_ctor_get(v_x_2471_, 1);
                    v_isSharedCheck_2543_ = (!leanh::lean_is_exclusive(v_x_2471_)) as u8;
                    if v_isSharedCheck_2543_ == 0 {
                        v___x_2525_ = v_x_2471_;
                        v_isShared_2526_ = v_isSharedCheck_2543_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2523_);
                        leanh::lean_inc(v_ks_2522_);
                        leanh::lean_dec(v_x_2471_);
                        v___x_2525_ = leanh::lean_box(0);
                        v_isShared_2526_ = v_isSharedCheck_2543_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2487_ = lean_array_fget(v_es_2476_, v_j_2481_);
                v___x_2488_ = leanh::lean_box(0);
                v_xs_x27_2489_ = lean_array_fset(v_es_2476_, v_j_2481_, v___x_2488_);
                match leanh::lean_obj_tag(v_v_2487_) {
                    0 => {
                        v_key_2496_ = leanh::lean_ctor_get(v_v_2487_, 0);
                        v_val_2497_ = leanh::lean_ctor_get(v_v_2487_, 1);
                        v_isSharedCheck_2507_ = (!leanh::lean_is_exclusive(v_v_2487_)) as u8;
                        if v_isSharedCheck_2507_ == 0 {
                            v___x_2499_ = v_v_2487_;
                            v_isShared_2500_ = v_isSharedCheck_2507_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2497_);
                            leanh::lean_inc(v_key_2496_);
                            leanh::lean_dec(v_v_2487_);
                            v___x_2499_ = leanh::lean_box(0);
                            v_isShared_2500_ = v_isSharedCheck_2507_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2508_ = leanh::lean_ctor_get(v_v_2487_, 0);
                        v_isSharedCheck_2518_ = (!leanh::lean_is_exclusive(v_v_2487_)) as u8;
                        if v_isSharedCheck_2518_ == 0 {
                            v___x_2510_ = v_v_2487_;
                            v_isShared_2511_ = v_isSharedCheck_2518_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2508_);
                            leanh::lean_dec(v_v_2487_);
                            v___x_2510_ = leanh::lean_box(0);
                            v_isShared_2511_ = v_isSharedCheck_2518_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2519_, 0, v_x_2474_);
                        leanh::lean_ctor_set(v___x_2519_, 1, v_x_2475_);
                        v___y_2491_ = v___x_2519_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2492_ = lean_array_fset(v_xs_x27_2489_, v_j_2481_, v___y_2491_);
                leanh::lean_dec(v_j_2481_);
                if v_isShared_2486_ == 0 {
                    leanh::lean_ctor_set(v___x_2485_, 0, v___x_2492_);
                    v___x_2494_ = v___x_2485_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2495_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
                    v___x_2494_ = v_reuseFailAlloc_2495_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2494_;
            }
            4 => {
                v___x_2501_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2474_, v_key_2496_);
                if v___x_2501_ == 0 {
                    leanh::lean_del_object(v___x_2499_);
                    v___x_2502_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2496_,
                        v_val_2497_,
                        v_x_2474_,
                        v_x_2475_,
                    );
                    v___x_2503_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2503_, 0, v___x_2502_);
                    v___y_2491_ = v___x_2503_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2497_);
                    leanh::lean_dec(v_key_2496_);
                    if v_isShared_2500_ == 0 {
                        leanh::lean_ctor_set(v___x_2499_, 1, v_x_2475_);
                        leanh::lean_ctor_set(v___x_2499_, 0, v_x_2474_);
                        v___x_2505_ = v___x_2499_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2506_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_x_2474_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_x_2475_);
                        v___x_2505_ = v_reuseFailAlloc_2506_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2491_ = v___x_2505_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2512_ = lean_usize_shift_right(v_x_2472_, v___x_2477_);
                v___x_2513_ = lean_usize_add(v_x_2473_, v___x_2478_);
                v___x_2514_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_node_2508_, v___x_2512_, v___x_2513_, v_x_2474_, v_x_2475_);
                if v_isShared_2511_ == 0 {
                    leanh::lean_ctor_set(v___x_2510_, 0, v___x_2514_);
                    v___x_2516_ = v___x_2510_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
                    v___x_2516_ = v_reuseFailAlloc_2517_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2491_ = v___x_2516_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2526_ == 0 {
                    v___x_2528_ = v___x_2525_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2542_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_ks_2522_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_vs_2523_);
                    v___x_2528_ = v_reuseFailAlloc_2542_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2529_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v___x_2528_, v_x_2474_, v_x_2475_);
                v___x_2537_ = 7usize;
                v___x_2538_ = lean_usize_dec_le(v___x_2537_, v_x_2473_);
                if v___x_2538_ == 0 {
                    v___x_2539_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2529_);
                    v___x_2540_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2541_ = lean_nat_dec_lt(v___x_2539_, v___x_2540_);
                    leanh::lean_dec(v___x_2539_);
                    v___y_2531_ = v___x_2541_;
                    state = 10;
                    continue;
                } else {
                    v___y_2531_ = v___x_2538_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2531_ == 0 {
                    v_ks_2532_ = leanh::lean_ctor_get(v_newNode_2529_, 0);
                    leanh::lean_inc_ref(v_ks_2532_);
                    v_vs_2533_ = leanh::lean_ctor_get(v_newNode_2529_, 1);
                    leanh::lean_inc_ref(v_vs_2533_);
                    leanh::lean_dec_ref(v_newNode_2529_);
                    v___x_2534_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2535_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0);
                    v___x_2536_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg(v_x_2473_, v_ks_2532_, v_vs_2533_, v___x_2534_, v___x_2535_);
                    leanh::lean_dec_ref(v_vs_2533_);
                    leanh::lean_dec_ref(v_ks_2532_);
                    return v___x_2536_;
                } else {
                    return v_newNode_2529_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg(
    mut v_depth_2544_: usize,
    mut v_keys_2545_: *mut leanh::LeanObject,
    mut v_vals_2546_: *mut leanh::LeanObject,
    mut v_i_2547_: *mut leanh::LeanObject,
    mut v_entries_2548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: u8 = 0;
    let mut v_k_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: u64 = 0;
    let mut v_h_2554_: usize = 0;
    let mut v___x_2555_: usize = 0;
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: usize = 0;
    let mut v___x_2558_: usize = 0;
    let mut v___x_2559_: usize = 0;
    let mut v_h_2560_: usize = 0;
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2549_ = lean_array_get_size(v_keys_2545_);
                v___x_2550_ = lean_nat_dec_lt(v_i_2547_, v___x_2549_);
                if v___x_2550_ == 0 {
                    leanh::lean_dec(v_i_2547_);
                    return v_entries_2548_;
                } else {
                    v_k_2551_ = lean_array_fget_borrowed(v_keys_2545_, v_i_2547_);
                    v_v_2552_ = lean_array_fget_borrowed(v_vals_2546_, v_i_2547_);
                    v___x_2553_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_2551_);
                    v_h_2554_ = lean_uint64_to_usize(v___x_2553_);
                    v___x_2555_ = 5usize;
                    v___x_2556_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2557_ = 1usize;
                    v___x_2558_ = lean_usize_sub(v_depth_2544_, v___x_2557_);
                    v___x_2559_ = lean_usize_mul(v___x_2555_, v___x_2558_);
                    v_h_2560_ = lean_usize_shift_right(v_h_2554_, v___x_2559_);
                    v___x_2561_ = lean_nat_add(v_i_2547_, v___x_2556_);
                    leanh::lean_dec(v_i_2547_);
                    leanh::lean_inc(v_v_2552_);
                    leanh::lean_inc(v_k_2551_);
                    v___x_2562_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_entries_2548_, v_h_2560_, v_depth_2544_, v_k_2551_, v_v_2552_);
                    v_i_2547_ = v___x_2561_;
                    v_entries_2548_ = v___x_2562_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_depth_2564_: *mut leanh::LeanObject,
    mut v_keys_2565_: *mut leanh::LeanObject,
    mut v_vals_2566_: *mut leanh::LeanObject,
    mut v_i_2567_: *mut leanh::LeanObject,
    mut v_entries_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2569_: usize = 0;
    let mut v_res_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2569_ = leanh::lean_unbox_usize(v_depth_2564_);
    leanh::lean_dec(v_depth_2564_);
    v_res_2570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg(v_depth_boxed_2569_, v_keys_2565_, v_vals_2566_, v_i_2567_, v_entries_2568_);
    leanh::lean_dec_ref(v_vals_2566_);
    leanh::lean_dec_ref(v_keys_2565_);
    return v_res_2570_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_2571_: *mut leanh::LeanObject,
    mut v_x_2572_: *mut leanh::LeanObject,
    mut v_x_2573_: *mut leanh::LeanObject,
    mut v_x_2574_: *mut leanh::LeanObject,
    mut v_x_2575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2336__boxed_2576_: usize = 0;
    let mut v_x_2337__boxed_2577_: usize = 0;
    let mut v_res_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2336__boxed_2576_ = leanh::lean_unbox_usize(v_x_2572_);
    leanh::lean_dec(v_x_2572_);
    v_x_2337__boxed_2577_ = leanh::lean_unbox_usize(v_x_2573_);
    leanh::lean_dec(v_x_2573_);
    v_res_2578_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2571_, v_x_2336__boxed_2576_, v_x_2337__boxed_2577_, v_x_2574_, v_x_2575_);
    return v_res_2578_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_x_2579_: *mut leanh::LeanObject,
    mut v_x_2580_: *mut leanh::LeanObject,
    mut v_x_2581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2582_: u64 = 0;
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: usize = 0;
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2582_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_2580_);
    v___x_2583_ = lean_uint64_to_usize(v___x_2582_);
    v___x_2584_ = 1usize;
    v___x_2585_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2579_, v___x_2583_, v___x_2584_, v_x_2580_, v_x_2581_);
    return v___x_2585_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2586_ = l_Lean_Meta_DiscrTree_instInhabited(leanh::lean_box(0));
    return v___x_2586_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3(
    mut v_msg_2587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2588_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0);
    v___x_2589_ = lean_panic_fn_borrowed(v___x_2588_, v_msg_2587_);
    return v___x_2589_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2;
    v___x_2594_ = leanh::lean_unsigned_to_nat(23);
    v___x_2595_ = leanh::lean_unsigned_to_nat(166);
    v___x_2596_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1;
    v___x_2597_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0;
    v___x_2598_ = l_mkPanicMessageWithDecl(
        v___x_2597_,
        v___x_2596_,
        v___x_2595_,
        v___x_2594_,
        v___x_2593_,
    );
    return v___x_2598_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(
    mut v_d_2599_: *mut leanh::LeanObject,
    mut v_keys_2600_: *mut leanh::LeanObject,
    mut v_v_2601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: u8 = 0;
    v___x_2602_ = lean_array_get_size(v_keys_2600_);
    v___x_2603_ = leanh::lean_unsigned_to_nat(0);
    v___x_2604_ = lean_nat_dec_eq(v___x_2602_, v___x_2603_);
    if v___x_2604_ == 0 {
        let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2605_ = leanh::lean_box(0);
        v_k_2606_ = lean_array_get_borrowed(v___x_2605_, v_keys_2600_, v___x_2603_);
        v___x_2607_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg(v_d_2599_, v_k_2606_);
        if leanh::lean_obj_tag(v___x_2607_) == 0 {
            let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2608_ = leanh::lean_unsigned_to_nat(1);
            v_c_2609_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                leanh::lean_box(0),
                v_keys_2600_,
                v_v_2601_,
                v___x_2608_,
            );
            leanh::lean_inc(v_k_2606_);
            v___x_2610_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_2599_, v_k_2606_, v_c_2609_);
            return v___x_2610_;
        } else {
            let mut v_val_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2611_ = leanh::lean_ctor_get(v___x_2607_, 0);
            leanh::lean_inc(v_val_2611_);
            leanh::lean_dec_ref_known(v___x_2607_, 1);
            v___x_2612_ = leanh::lean_unsigned_to_nat(1);
            v_c_2613_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v_keys_2600_, v_v_2601_, v___x_2612_, v_val_2611_);
            leanh::lean_inc(v_k_2606_);
            v___x_2614_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_2599_, v_k_2606_, v_c_2613_);
            return v___x_2614_;
        }
    } else {
        let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_v_2601_);
        leanh::lean_dec_ref(v_d_2599_);
        v___x_2615_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3);
        v___x_2616_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3(v___x_2615_);
        return v___x_2616_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___boxed(
    mut v_d_2617_: *mut leanh::LeanObject,
    mut v_keys_2618_: *mut leanh::LeanObject,
    mut v_v_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2620_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_d_2617_, v_keys_2618_, v_v_2619_);
    leanh::lean_dec_ref(v_keys_2618_);
    return v_res_2620_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(
    mut v_x_2621_: *mut leanh::LeanObject,
    mut v_thm_2622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tree_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2627_: u8 = 0;
    let mut v_declName_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tree_2623_ = leanh::lean_ctor_get(v_x_2621_, 0);
                v_erased_2624_ = leanh::lean_ctor_get(v_x_2621_, 1);
                v_isSharedCheck_2635_ = (!leanh::lean_is_exclusive(v_x_2621_)) as u8;
                if v_isSharedCheck_2635_ == 0 {
                    v___x_2626_ = v_x_2621_;
                    v_isShared_2627_ = v_isSharedCheck_2635_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_erased_2624_);
                    leanh::lean_inc(v_tree_2623_);
                    leanh::lean_dec(v_x_2621_);
                    v___x_2626_ = leanh::lean_box(0);
                    v_isShared_2627_ = v_isSharedCheck_2635_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_declName_2628_ = leanh::lean_ctor_get(v_thm_2622_, 0);
                leanh::lean_inc(v_declName_2628_);
                v_keys_2629_ = leanh::lean_ctor_get(v_thm_2622_, 2);
                leanh::lean_inc_ref(v_keys_2629_);
                v___x_2630_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_tree_2623_, v_keys_2629_, v_thm_2622_);
                leanh::lean_dec_ref(v_keys_2629_);
                v___x_2631_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_erased_2624_, v_declName_2628_);
                leanh::lean_dec(v_declName_2628_);
                if v_isShared_2627_ == 0 {
                    leanh::lean_ctor_set(v___x_2626_, 1, v___x_2631_);
                    leanh::lean_ctor_set(v___x_2626_, 0, v___x_2630_);
                    v___x_2633_ = v___x_2626_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2634_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 1, v___x_2631_);
                    v___x_2633_ = v_reuseFailAlloc_2634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(
    mut v___y_2636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___y_2636_);
    return v___y_2636_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(
    mut v___y_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2638_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v___y_2637_);
    leanh::lean_dec_ref(v___y_2637_);
    return v_res_2638_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2651_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_;
    v___f_2652_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_;
    v___x_2653_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once),
        _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3,
    );
    v___f_2654_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_;
    v___x_2655_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_;
    v___x_2656_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2656_, 0, v___x_2655_);
    leanh::lean_ctor_set(v___x_2656_, 1, v___f_2654_);
    leanh::lean_ctor_set(v___x_2656_, 2, v___x_2653_);
    leanh::lean_ctor_set(v___x_2656_, 3, v___f_2652_);
    leanh::lean_ctor_set(v___x_2656_, 4, v___f_2651_);
    return v___x_2656_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2658_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_);
    v___x_2659_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2658_);
    return v___x_2659_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(
    mut v_a_2660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2661_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_();
    return v_res_2661_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(
    mut v_00_u03b2_2662_: *mut leanh::LeanObject,
    mut v_x_2663_: *mut leanh::LeanObject,
    mut v_x_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_2663_, v_x_2664_);
    return v___x_2665_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b2_2666_: *mut leanh::LeanObject,
    mut v_x_2667_: *mut leanh::LeanObject,
    mut v_x_2668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2669_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(v_00_u03b2_2666_, v_x_2667_, v_x_2668_);
    leanh::lean_dec(v_x_2668_);
    return v_res_2669_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_2670_: *mut leanh::LeanObject,
    mut v_x_2671_: *mut leanh::LeanObject,
    mut v_x_2672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2673_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2671_, v_x_2672_);
    return v___x_2673_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_2674_: *mut leanh::LeanObject,
    mut v_x_2675_: *mut leanh::LeanObject,
    mut v_x_2676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2677_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_2674_, v_x_2675_, v_x_2676_);
    leanh::lean_dec(v_x_2676_);
    leanh::lean_dec_ref(v_x_2675_);
    return v_res_2677_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_2678_: *mut leanh::LeanObject,
    mut v_x_2679_: *mut leanh::LeanObject,
    mut v_x_2680_: *mut leanh::LeanObject,
    mut v_x_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_2679_, v_x_2680_, v_x_2681_);
    return v___x_2682_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5(
    mut v_00_u03b2_2683_: *mut leanh::LeanObject,
    mut v_x_2684_: *mut leanh::LeanObject,
    mut v_x_2685_: usize,
    mut v_x_2686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2687_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(v_x_2684_, v_x_2685_, v_x_2686_);
    return v___x_2687_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___boxed(
    mut v_00_u03b2_2688_: *mut leanh::LeanObject,
    mut v_x_2689_: *mut leanh::LeanObject,
    mut v_x_2690_: *mut leanh::LeanObject,
    mut v_x_2691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2683__boxed_2692_: usize = 0;
    let mut v_res_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2683__boxed_2692_ = leanh::lean_unbox_usize(v_x_2690_);
    leanh::lean_dec(v_x_2690_);
    v_res_2693_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5(v_00_u03b2_2688_, v_x_2689_, v_x_2683__boxed_2692_, v_x_2691_);
    leanh::lean_dec(v_x_2691_);
    return v_res_2693_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_2694_: *mut leanh::LeanObject,
    mut v_x_2695_: *mut leanh::LeanObject,
    mut v_x_2696_: usize,
    mut v_x_2697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2698_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2695_, v_x_2696_, v_x_2697_);
    return v___x_2698_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2699_: *mut leanh::LeanObject,
    mut v_x_2700_: *mut leanh::LeanObject,
    mut v_x_2701_: *mut leanh::LeanObject,
    mut v_x_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2694__boxed_2703_: usize = 0;
    let mut v_res_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2694__boxed_2703_ = leanh::lean_unbox_usize(v_x_2701_);
    leanh::lean_dec(v_x_2701_);
    v_res_2704_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2699_, v_x_2700_, v_x_2694__boxed_2703_, v_x_2702_);
    leanh::lean_dec(v_x_2702_);
    leanh::lean_dec_ref(v_x_2700_);
    return v_res_2704_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3(
    mut v_00_u03b2_2705_: *mut leanh::LeanObject,
    mut v_x_2706_: *mut leanh::LeanObject,
    mut v_x_2707_: usize,
    mut v_x_2708_: usize,
    mut v_x_2709_: *mut leanh::LeanObject,
    mut v_x_2710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2711_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2706_, v_x_2707_, v_x_2708_, v_x_2709_, v_x_2710_);
    return v___x_2711_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2712_: *mut leanh::LeanObject,
    mut v_x_2713_: *mut leanh::LeanObject,
    mut v_x_2714_: *mut leanh::LeanObject,
    mut v_x_2715_: *mut leanh::LeanObject,
    mut v_x_2716_: *mut leanh::LeanObject,
    mut v_x_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2705__boxed_2718_: usize = 0;
    let mut v_x_2706__boxed_2719_: usize = 0;
    let mut v_res_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2705__boxed_2718_ = leanh::lean_unbox_usize(v_x_2714_);
    leanh::lean_dec(v_x_2714_);
    v_x_2706__boxed_2719_ = leanh::lean_unbox_usize(v_x_2715_);
    leanh::lean_dec(v_x_2715_);
    v_res_2720_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_2712_, v_x_2713_, v_x_2705__boxed_2718_, v_x_2706__boxed_2719_, v_x_2716_, v_x_2717_);
    return v_res_2720_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_2721_: *mut leanh::LeanObject,
    mut v_keys_2722_: *mut leanh::LeanObject,
    mut v_vals_2723_: *mut leanh::LeanObject,
    mut v_heq_2724_: *mut leanh::LeanObject,
    mut v_i_2725_: *mut leanh::LeanObject,
    mut v_k_2726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2727_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_keys_2722_, v_vals_2723_, v_i_2725_, v_k_2726_);
    return v___x_2727_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_2728_: *mut leanh::LeanObject,
    mut v_keys_2729_: *mut leanh::LeanObject,
    mut v_vals_2730_: *mut leanh::LeanObject,
    mut v_heq_2731_: *mut leanh::LeanObject,
    mut v_i_2732_: *mut leanh::LeanObject,
    mut v_k_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b2_2728_, v_keys_2729_, v_vals_2730_, v_heq_2731_, v_i_2732_, v_k_2733_);
    leanh::lean_dec(v_k_2733_);
    leanh::lean_dec_ref(v_vals_2730_);
    leanh::lean_dec_ref(v_keys_2729_);
    return v_res_2734_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_2735_: *mut leanh::LeanObject,
    mut v_n_2736_: *mut leanh::LeanObject,
    mut v_k_2737_: *mut leanh::LeanObject,
    mut v_v_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2739_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_n_2736_, v_k_2737_, v_v_2738_);
    return v___x_2739_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8(
    mut v_00_u03b2_2740_: *mut leanh::LeanObject,
    mut v_depth_2741_: usize,
    mut v_keys_2742_: *mut leanh::LeanObject,
    mut v_vals_2743_: *mut leanh::LeanObject,
    mut v_heq_2744_: *mut leanh::LeanObject,
    mut v_i_2745_: *mut leanh::LeanObject,
    mut v_entries_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2747_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg(v_depth_2741_, v_keys_2742_, v_vals_2743_, v_i_2745_, v_entries_2746_);
    return v___x_2747_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_2748_: *mut leanh::LeanObject,
    mut v_depth_2749_: *mut leanh::LeanObject,
    mut v_keys_2750_: *mut leanh::LeanObject,
    mut v_vals_2751_: *mut leanh::LeanObject,
    mut v_heq_2752_: *mut leanh::LeanObject,
    mut v_i_2753_: *mut leanh::LeanObject,
    mut v_entries_2754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2755_: usize = 0;
    let mut v_res_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2755_ = leanh::lean_unbox_usize(v_depth_2749_);
    leanh::lean_dec(v_depth_2749_);
    v_res_2756_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8(v_00_u03b2_2748_, v_depth_boxed_2755_, v_keys_2750_, v_vals_2751_, v_heq_2752_, v_i_2753_, v_entries_2754_);
    leanh::lean_dec_ref(v_vals_2751_);
    leanh::lean_dec_ref(v_keys_2750_);
    return v_res_2756_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13(
    mut v_x_2757_: *mut leanh::LeanObject,
    mut v_keys_2758_: *mut leanh::LeanObject,
    mut v_v_2759_: *mut leanh::LeanObject,
    mut v_k_2760_: *mut leanh::LeanObject,
    mut v_as_2761_: *mut leanh::LeanObject,
    mut v_k_2762_: *mut leanh::LeanObject,
    mut v_x_2763_: *mut leanh::LeanObject,
    mut v_x_2764_: *mut leanh::LeanObject,
    mut v_x_2765_: *mut leanh::LeanObject,
    mut v_x_2766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2767_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg(v_x_2757_, v_keys_2758_, v_v_2759_, v_k_2760_, v_as_2761_, v_k_2762_, v_x_2763_, v_x_2764_);
    return v___x_2767_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___boxed(
    mut v_x_2768_: *mut leanh::LeanObject,
    mut v_keys_2769_: *mut leanh::LeanObject,
    mut v_v_2770_: *mut leanh::LeanObject,
    mut v_k_2771_: *mut leanh::LeanObject,
    mut v_as_2772_: *mut leanh::LeanObject,
    mut v_k_2773_: *mut leanh::LeanObject,
    mut v_x_2774_: *mut leanh::LeanObject,
    mut v_x_2775_: *mut leanh::LeanObject,
    mut v_x_2776_: *mut leanh::LeanObject,
    mut v_x_2777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2778_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13(v_x_2768_, v_keys_2769_, v_v_2770_, v_k_2771_, v_as_2772_, v_k_2773_, v_x_2774_, v_x_2775_, v_x_2776_, v_x_2777_);
    leanh::lean_dec_ref(v_k_2773_);
    leanh::lean_dec_ref(v_keys_2769_);
    leanh::lean_dec(v_x_2768_);
    return v_res_2778_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10(
    mut v_00_u03b2_2779_: *mut leanh::LeanObject,
    mut v_x_2780_: *mut leanh::LeanObject,
    mut v_x_2781_: *mut leanh::LeanObject,
    mut v_x_2782_: *mut leanh::LeanObject,
    mut v_x_2783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2784_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_x_2780_, v_x_2781_, v_x_2782_, v_x_2783_);
    return v___x_2784_;
}
pub unsafe fn l_Lean_Meta_Ext_getExtTheorems___lam__0(
    mut v_x1_2785_: *mut leanh::LeanObject,
    mut v_x2_2786_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_priority_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: u8 = 0;
    v_priority_2787_ = leanh::lean_ctor_get(v_x1_2785_, 1);
    v_priority_2788_ = leanh::lean_ctor_get(v_x2_2786_, 1);
    v___x_2789_ = lean_nat_dec_lt(v_priority_2787_, v_priority_2788_);
    return v___x_2789_;
}
pub unsafe fn l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed(
    mut v_x1_2790_: *mut leanh::LeanObject,
    mut v_x2_2791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2792_: u8 = 0;
    let mut v_r_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_Meta_Ext_getExtTheorems___lam__0(v_x1_2790_, v_x2_2791_);
    leanh::lean_dec_ref(v_x2_2791_);
    leanh::lean_dec_ref(v_x1_2790_);
    v_r_2793_ = leanh::lean_box((v_res_2792_) as usize);
    return v_r_2793_;
}
pub unsafe fn l_Lean_Meta_Ext_getExtTheorems___lam__1(
    mut v___x_2794_: *mut leanh::LeanObject,
    mut v___x_2795_: *mut leanh::LeanObject,
    mut v___x_2796_: *mut leanh::LeanObject,
    mut v_x1_2797_: *mut leanh::LeanObject,
    mut v_x2_2798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_erased_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: u8 = 0;
    v_erased_2799_ = leanh::lean_ctor_get(v___x_2794_, 1);
    leanh::lean_inc_ref(v_erased_2799_);
    leanh::lean_dec_ref(v___x_2794_);
    v_declName_2800_ = leanh::lean_ctor_get(v_x2_2798_, 0);
    leanh::lean_inc(v_declName_2800_);
    v___x_2801_ = l_Lean_PersistentHashMap_contains___redArg(
        v___x_2795_,
        v___x_2796_,
        v_erased_2799_,
        v_declName_2800_,
    );
    if v___x_2801_ == 0 {
        let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2802_ = lean_array_push(v_x1_2797_, v_x2_2798_);
        return v___x_2802_;
    } else {
        leanh::lean_dec_ref(v_x2_2798_);
        return v_x1_2797_;
    }
}
pub unsafe fn l_Lean_Meta_Ext_getExtTheorems(
    mut v_ty_2825_: *mut leanh::LeanObject,
    mut v_a_2826_: *mut leanh::LeanObject,
    mut v_a_2827_: *mut leanh::LeanObject,
    mut v_a_2828_: *mut leanh::LeanObject,
    mut v_a_2829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v___f_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: u8 = 0;
    let mut v___x_2864_: usize = 0;
    let mut v___x_2865_: usize = 0;
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: usize = 0;
    let mut v___x_2868_: usize = 0;
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2831_ = lean_st_ref_get(v_a_2829_);
                v_env_2832_ = leanh::lean_ctor_get(v___x_2831_, 0);
                leanh::lean_inc_ref(v_env_2832_);
                leanh::lean_dec(v___x_2831_);
                v___x_2833_ = l_Lean_Meta_Ext_extExtension;
                v_ext_2834_ = leanh::lean_ctor_get(v___x_2833_, 1);
                v_toEnvExtension_2835_ = leanh::lean_ctor_get(v_ext_2834_, 0);
                v_asyncMode_2836_ = leanh::lean_ctor_get(v_toEnvExtension_2835_, 2);
                v___x_2837_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
                v___x_2838_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_2837_,
                    v___x_2833_,
                    v_env_2832_,
                    v_asyncMode_2836_,
                );
                v_tree_2839_ = leanh::lean_ctor_get(v___x_2838_, 0);
                leanh::lean_inc_ref(v_tree_2839_);
                v___x_2840_ = l_Lean_Meta_DiscrTree_getMatch___redArg(
                    v_tree_2839_,
                    v_ty_2825_,
                    v_a_2826_,
                    v_a_2827_,
                    v_a_2828_,
                    v_a_2829_,
                );
                leanh::lean_dec_ref(v_tree_2839_);
                if leanh::lean_obj_tag(v___x_2840_) == 0 {
                    v_a_2841_ = leanh::lean_ctor_get(v___x_2840_, 0);
                    v_isSharedCheck_2870_ = (!leanh::lean_is_exclusive(v___x_2840_)) as u8;
                    if v_isSharedCheck_2870_ == 0 {
                        v___x_2843_ = v___x_2840_;
                        v_isShared_2844_ = v_isSharedCheck_2870_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2841_);
                        leanh::lean_dec(v___x_2840_);
                        v___x_2843_ = leanh::lean_box(0);
                        v_isShared_2844_ = v_isSharedCheck_2870_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2838_);
                    return v___x_2840_;
                }
            }
            1 => {
                v___f_2845_ = l_Lean_Meta_Ext_getExtTheorems___closed__0;
                v___x_2855_ = leanh::lean_unsigned_to_nat(0);
                v___x_2856_ = lean_array_get_size(v_a_2841_);
                v___x_2857_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0;
                v___x_2858_ = l_Lean_Meta_Ext_getExtTheorems___closed__10;
                v___x_2859_ = lean_nat_dec_lt(v___x_2855_, v___x_2856_);
                if v___x_2859_ == 0 {
                    leanh::lean_dec(v_a_2841_);
                    leanh::lean_dec(v___x_2838_);
                    v___y_2847_ = v___x_2857_;
                    state = 2;
                    continue;
                } else {
                    v___x_2860_ = l_Lean_Meta_Ext_getExtTheorems___closed__11;
                    v___x_2861_ = l_Lean_Meta_Ext_getExtTheorems___closed__12;
                    v___f_2862_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Ext_getExtTheorems___lam__1 as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2862_, 0, v___x_2838_);
                    leanh::lean_closure_set(v___f_2862_, 1, v___x_2860_);
                    leanh::lean_closure_set(v___f_2862_, 2, v___x_2861_);
                    v___x_2863_ = lean_nat_dec_le(v___x_2856_, v___x_2856_);
                    if v___x_2863_ == 0 {
                        if v___x_2859_ == 0 {
                            leanh::lean_dec_ref(v___f_2862_);
                            leanh::lean_dec(v_a_2841_);
                            v___y_2847_ = v___x_2857_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2864_ = 0usize;
                            v___x_2865_ = lean_usize_of_nat(v___x_2856_);
                            v___x_2866_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2858_,
                                    v___f_2862_,
                                    v_a_2841_,
                                    v___x_2864_,
                                    v___x_2865_,
                                    v___x_2857_,
                                );
                            v___y_2847_ = v___x_2866_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2867_ = 0usize;
                        v___x_2868_ = lean_usize_of_nat(v___x_2856_);
                        v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2858_,
                            v___f_2862_,
                            v_a_2841_,
                            v___x_2867_,
                            v___x_2868_,
                            v___x_2857_,
                        );
                        v___y_2847_ = v___x_2869_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2848_ = leanh::lean_unsigned_to_nat(0);
                v___x_2849_ = lean_array_get_size(v___y_2847_);
                v___x_2850_ =
                    l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse(
                        leanh::lean_box(0),
                        v___f_2845_,
                        v___y_2847_,
                        v___x_2848_,
                        v___x_2849_,
                    );
                v___x_2851_ = l_Array_reverse___redArg(v___x_2850_);
                if v_isShared_2844_ == 0 {
                    leanh::lean_ctor_set(v___x_2843_, 0, v___x_2851_);
                    v___x_2853_ = v___x_2843_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2854_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
                    v___x_2853_ = v_reuseFailAlloc_2854_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Ext_getExtTheorems___boxed(
    mut v_ty_2871_: *mut leanh::LeanObject,
    mut v_a_2872_: *mut leanh::LeanObject,
    mut v_a_2873_: *mut leanh::LeanObject,
    mut v_a_2874_: *mut leanh::LeanObject,
    mut v_a_2875_: *mut leanh::LeanObject,
    mut v_a_2876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2877_ =
        l_Lean_Meta_Ext_getExtTheorems(v_ty_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
    leanh::lean_dec(v_a_2875_);
    leanh::lean_dec_ref(v_a_2874_);
    leanh::lean_dec(v_a_2873_);
    leanh::lean_dec_ref(v_a_2872_);
    return v_res_2877_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2878_: *mut leanh::LeanObject,
    mut v_x_2879_: *mut leanh::LeanObject,
    mut v_x_2880_: *mut leanh::LeanObject,
    mut v_x_2881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2907_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2882_ = leanh::lean_ctor_get(v_x_2878_, 0);
                v_vs_2883_ = leanh::lean_ctor_get(v_x_2878_, 1);
                v_isSharedCheck_2907_ = (!leanh::lean_is_exclusive(v_x_2878_)) as u8;
                if v_isSharedCheck_2907_ == 0 {
                    v___x_2885_ = v_x_2878_;
                    v_isShared_2886_ = v_isSharedCheck_2907_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2883_);
                    leanh::lean_inc(v_ks_2882_);
                    leanh::lean_dec(v_x_2878_);
                    v___x_2885_ = leanh::lean_box(0);
                    v_isShared_2886_ = v_isSharedCheck_2907_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2887_ = lean_array_get_size(v_ks_2882_);
                v___x_2888_ = lean_nat_dec_lt(v_x_2879_, v___x_2887_);
                if v___x_2888_ == 0 {
                    leanh::lean_dec(v_x_2879_);
                    v___x_2889_ = lean_array_push(v_ks_2882_, v_x_2880_);
                    v___x_2890_ = lean_array_push(v_vs_2883_, v_x_2881_);
                    if v_isShared_2886_ == 0 {
                        leanh::lean_ctor_set(v___x_2885_, 1, v___x_2890_);
                        leanh::lean_ctor_set(v___x_2885_, 0, v___x_2889_);
                        v___x_2892_ = v___x_2885_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2893_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2889_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 1, v___x_2890_);
                        v___x_2892_ = v_reuseFailAlloc_2893_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2894_ = lean_array_fget_borrowed(v_ks_2882_, v_x_2879_);
                    v___x_2895_ = lean_name_eq(v_x_2880_, v_k_x27_2894_);
                    if v___x_2895_ == 0 {
                        if v_isShared_2886_ == 0 {
                            v___x_2897_ = v___x_2885_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2901_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_ks_2882_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_vs_2883_);
                            v___x_2897_ = v_reuseFailAlloc_2901_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2902_ = lean_array_fset(v_ks_2882_, v_x_2879_, v_x_2880_);
                        v___x_2903_ = lean_array_fset(v_vs_2883_, v_x_2879_, v_x_2881_);
                        leanh::lean_dec(v_x_2879_);
                        if v_isShared_2886_ == 0 {
                            leanh::lean_ctor_set(v___x_2885_, 1, v___x_2903_);
                            leanh::lean_ctor_set(v___x_2885_, 0, v___x_2902_);
                            v___x_2905_ = v___x_2885_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2906_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2902_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2906_, 1, v___x_2903_);
                            v___x_2905_ = v_reuseFailAlloc_2906_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2892_;
            }
            3 => {
                v___x_2898_ = leanh::lean_unsigned_to_nat(1);
                v___x_2899_ = lean_nat_add(v_x_2879_, v___x_2898_);
                leanh::lean_dec(v_x_2879_);
                v_x_2878_ = v___x_2897_;
                v_x_2879_ = v___x_2899_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(
    mut v_n_2908_: *mut leanh::LeanObject,
    mut v_k_2909_: *mut leanh::LeanObject,
    mut v_v_2910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2911_ = leanh::lean_unsigned_to_nat(0);
    v___x_2912_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2908_, v___x_2911_, v_k_2909_, v_v_2910_);
    return v___x_2912_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2913_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2913_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(
    mut v_x_2914_: *mut leanh::LeanObject,
    mut v_x_2915_: usize,
    mut v_x_2916_: usize,
    mut v_x_2917_: *mut leanh::LeanObject,
    mut v_x_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: usize = 0;
    let mut v___x_2921_: usize = 0;
    let mut v___x_2922_: usize = 0;
    let mut v___x_2923_: usize = 0;
    let mut v_j_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v_v_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2944_: u8 = 0;
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2950_: u8 = 0;
    let mut v_node_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2954_: u8 = 0;
    let mut v___x_2955_: usize = 0;
    let mut v___x_2956_: usize = 0;
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut v_unused_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: u8 = 0;
    let mut v_ks_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: usize = 0;
    let mut v___x_2981_: u8 = 0;
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: u8 = 0;
    let mut v_reuseFailAlloc_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2914_) == 0 {
                    v_es_2919_ = leanh::lean_ctor_get(v_x_2914_, 0);
                    v___x_2920_ = 5usize;
                    v___x_2921_ = 1usize;
                    v___x_2922_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
                    v___x_2923_ = lean_usize_land(v_x_2915_, v___x_2922_);
                    v_j_2924_ = lean_usize_to_nat(v___x_2923_);
                    v___x_2925_ = lean_array_get_size(v_es_2919_);
                    v___x_2926_ = lean_nat_dec_lt(v_j_2924_, v___x_2925_);
                    if v___x_2926_ == 0 {
                        leanh::lean_dec(v_j_2924_);
                        leanh::lean_dec(v_x_2918_);
                        leanh::lean_dec(v_x_2917_);
                        return v_x_2914_;
                    } else {
                        leanh::lean_inc_ref(v_es_2919_);
                        v_isSharedCheck_2963_ = (!leanh::lean_is_exclusive(v_x_2914_)) as u8;
                        if v_isSharedCheck_2963_ == 0 {
                            v_unused_2964_ = leanh::lean_ctor_get(v_x_2914_, 0);
                            leanh::lean_dec(v_unused_2964_);
                            v___x_2928_ = v_x_2914_;
                            v_isShared_2929_ = v_isSharedCheck_2963_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2914_);
                            v___x_2928_ = leanh::lean_box(0);
                            v_isShared_2929_ = v_isSharedCheck_2963_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2965_ = leanh::lean_ctor_get(v_x_2914_, 0);
                    v_vs_2966_ = leanh::lean_ctor_get(v_x_2914_, 1);
                    v_isSharedCheck_2986_ = (!leanh::lean_is_exclusive(v_x_2914_)) as u8;
                    if v_isSharedCheck_2986_ == 0 {
                        v___x_2968_ = v_x_2914_;
                        v_isShared_2969_ = v_isSharedCheck_2986_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2966_);
                        leanh::lean_inc(v_ks_2965_);
                        leanh::lean_dec(v_x_2914_);
                        v___x_2968_ = leanh::lean_box(0);
                        v_isShared_2969_ = v_isSharedCheck_2986_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2930_ = lean_array_fget(v_es_2919_, v_j_2924_);
                v___x_2931_ = leanh::lean_box(0);
                v_xs_x27_2932_ = lean_array_fset(v_es_2919_, v_j_2924_, v___x_2931_);
                match leanh::lean_obj_tag(v_v_2930_) {
                    0 => {
                        v_key_2939_ = leanh::lean_ctor_get(v_v_2930_, 0);
                        v_val_2940_ = leanh::lean_ctor_get(v_v_2930_, 1);
                        v_isSharedCheck_2950_ = (!leanh::lean_is_exclusive(v_v_2930_)) as u8;
                        if v_isSharedCheck_2950_ == 0 {
                            v___x_2942_ = v_v_2930_;
                            v_isShared_2943_ = v_isSharedCheck_2950_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2940_);
                            leanh::lean_inc(v_key_2939_);
                            leanh::lean_dec(v_v_2930_);
                            v___x_2942_ = leanh::lean_box(0);
                            v_isShared_2943_ = v_isSharedCheck_2950_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2951_ = leanh::lean_ctor_get(v_v_2930_, 0);
                        v_isSharedCheck_2961_ = (!leanh::lean_is_exclusive(v_v_2930_)) as u8;
                        if v_isSharedCheck_2961_ == 0 {
                            v___x_2953_ = v_v_2930_;
                            v_isShared_2954_ = v_isSharedCheck_2961_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2951_);
                            leanh::lean_dec(v_v_2930_);
                            v___x_2953_ = leanh::lean_box(0);
                            v_isShared_2954_ = v_isSharedCheck_2961_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2962_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2962_, 0, v_x_2917_);
                        leanh::lean_ctor_set(v___x_2962_, 1, v_x_2918_);
                        v___y_2934_ = v___x_2962_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2935_ = lean_array_fset(v_xs_x27_2932_, v_j_2924_, v___y_2934_);
                leanh::lean_dec(v_j_2924_);
                if v_isShared_2929_ == 0 {
                    leanh::lean_ctor_set(v___x_2928_, 0, v___x_2935_);
                    v___x_2937_ = v___x_2928_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2938_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2935_);
                    v___x_2937_ = v_reuseFailAlloc_2938_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2937_;
            }
            4 => {
                v___x_2944_ = lean_name_eq(v_x_2917_, v_key_2939_);
                if v___x_2944_ == 0 {
                    leanh::lean_del_object(v___x_2942_);
                    v___x_2945_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2939_,
                        v_val_2940_,
                        v_x_2917_,
                        v_x_2918_,
                    );
                    v___x_2946_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2946_, 0, v___x_2945_);
                    v___y_2934_ = v___x_2946_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2940_);
                    leanh::lean_dec(v_key_2939_);
                    if v_isShared_2943_ == 0 {
                        leanh::lean_ctor_set(v___x_2942_, 1, v_x_2918_);
                        leanh::lean_ctor_set(v___x_2942_, 0, v_x_2917_);
                        v___x_2948_ = v___x_2942_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2949_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_x_2917_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_x_2918_);
                        v___x_2948_ = v_reuseFailAlloc_2949_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2934_ = v___x_2948_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2955_ = lean_usize_shift_right(v_x_2915_, v___x_2920_);
                v___x_2956_ = lean_usize_add(v_x_2916_, v___x_2921_);
                v___x_2957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_node_2951_, v___x_2955_, v___x_2956_, v_x_2917_, v_x_2918_);
                if v_isShared_2954_ == 0 {
                    leanh::lean_ctor_set(v___x_2953_, 0, v___x_2957_);
                    v___x_2959_ = v___x_2953_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2957_);
                    v___x_2959_ = v_reuseFailAlloc_2960_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2934_ = v___x_2959_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2969_ == 0 {
                    v___x_2971_ = v___x_2968_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2985_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_ks_2965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_vs_2966_);
                    v___x_2971_ = v_reuseFailAlloc_2985_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2972_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v___x_2971_, v_x_2917_, v_x_2918_);
                v___x_2980_ = 7usize;
                v___x_2981_ = lean_usize_dec_le(v___x_2980_, v_x_2916_);
                if v___x_2981_ == 0 {
                    v___x_2982_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2972_);
                    v___x_2983_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2984_ = lean_nat_dec_lt(v___x_2982_, v___x_2983_);
                    leanh::lean_dec(v___x_2982_);
                    v___y_2974_ = v___x_2984_;
                    state = 10;
                    continue;
                } else {
                    v___y_2974_ = v___x_2981_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2974_ == 0 {
                    v_ks_2975_ = leanh::lean_ctor_get(v_newNode_2972_, 0);
                    leanh::lean_inc_ref(v_ks_2975_);
                    v_vs_2976_ = leanh::lean_ctor_get(v_newNode_2972_, 1);
                    leanh::lean_inc_ref(v_vs_2976_);
                    leanh::lean_dec_ref(v_newNode_2972_);
                    v___x_2977_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2978_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0);
                    v___x_2979_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_x_2916_, v_ks_2975_, v_vs_2976_, v___x_2977_, v___x_2978_);
                    leanh::lean_dec_ref(v_vs_2976_);
                    leanh::lean_dec_ref(v_ks_2975_);
                    return v___x_2979_;
                } else {
                    return v_newNode_2972_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(
    mut v_depth_2987_: usize,
    mut v_keys_2988_: *mut leanh::LeanObject,
    mut v_vals_2989_: *mut leanh::LeanObject,
    mut v_i_2990_: *mut leanh::LeanObject,
    mut v_entries_2991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: u8 = 0;
    let mut v_k_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2997_: u64 = 0;
    let mut v_h_2998_: usize = 0;
    let mut v___x_2999_: usize = 0;
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: usize = 0;
    let mut v___x_3002_: usize = 0;
    let mut v___x_3003_: usize = 0;
    let mut v_h_3004_: usize = 0;
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u64 = 0;
    let mut v_hash_3009_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2992_ = lean_array_get_size(v_keys_2988_);
                v___x_2993_ = lean_nat_dec_lt(v_i_2990_, v___x_2992_);
                if v___x_2993_ == 0 {
                    leanh::lean_dec(v_i_2990_);
                    return v_entries_2991_;
                } else {
                    v_k_2994_ = lean_array_fget_borrowed(v_keys_2988_, v_i_2990_);
                    v_v_2995_ = lean_array_fget_borrowed(v_vals_2989_, v_i_2990_);
                    if leanh::lean_obj_tag(v_k_2994_) == 0 {
                        v___x_3008_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once
                            ),
                            _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0,
                        );
                        v___y_2997_ = v___x_3008_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3009_ = leanh::lean_ctor_get_uint64(
                            v_k_2994_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2997_ = v_hash_3009_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2998_ = lean_uint64_to_usize(v___y_2997_);
                v___x_2999_ = 5usize;
                v___x_3000_ = leanh::lean_unsigned_to_nat(1);
                v___x_3001_ = 1usize;
                v___x_3002_ = lean_usize_sub(v_depth_2987_, v___x_3001_);
                v___x_3003_ = lean_usize_mul(v___x_2999_, v___x_3002_);
                v_h_3004_ = lean_usize_shift_right(v_h_2998_, v___x_3003_);
                v___x_3005_ = lean_nat_add(v_i_2990_, v___x_3000_);
                leanh::lean_dec(v_i_2990_);
                leanh::lean_inc(v_v_2995_);
                leanh::lean_inc(v_k_2994_);
                v___x_3006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_entries_2991_, v_h_3004_, v_depth_2987_, v_k_2994_, v_v_2995_);
                v_i_2990_ = v___x_3005_;
                v_entries_2991_ = v___x_3006_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_3010_: *mut leanh::LeanObject,
    mut v_keys_3011_: *mut leanh::LeanObject,
    mut v_vals_3012_: *mut leanh::LeanObject,
    mut v_i_3013_: *mut leanh::LeanObject,
    mut v_entries_3014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3015_: usize = 0;
    let mut v_res_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3015_ = leanh::lean_unbox_usize(v_depth_3010_);
    leanh::lean_dec(v_depth_3010_);
    v_res_3016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_3015_, v_keys_3011_, v_vals_3012_, v_i_3013_, v_entries_3014_);
    leanh::lean_dec_ref(v_vals_3012_);
    leanh::lean_dec_ref(v_keys_3011_);
    return v_res_3016_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___boxed(
    mut v_x_3017_: *mut leanh::LeanObject,
    mut v_x_3018_: *mut leanh::LeanObject,
    mut v_x_3019_: *mut leanh::LeanObject,
    mut v_x_3020_: *mut leanh::LeanObject,
    mut v_x_3021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_371__boxed_3022_: usize = 0;
    let mut v_x_372__boxed_3023_: usize = 0;
    let mut v_res_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_371__boxed_3022_ = leanh::lean_unbox_usize(v_x_3018_);
    leanh::lean_dec(v_x_3018_);
    v_x_372__boxed_3023_ = leanh::lean_unbox_usize(v_x_3019_);
    leanh::lean_dec(v_x_3019_);
    v_res_3024_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_3017_, v_x_371__boxed_3022_, v_x_372__boxed_3023_, v_x_3020_, v_x_3021_);
    return v_res_3024_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(
    mut v_x_3025_: *mut leanh::LeanObject,
    mut v_x_3026_: *mut leanh::LeanObject,
    mut v_x_3027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3029_: u64 = 0;
    let mut v___x_3030_: usize = 0;
    let mut v___x_3031_: usize = 0;
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: u64 = 0;
    let mut v_hash_3034_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3026_) == 0 {
                    v___x_3033_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once
                        ),
                        _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0,
                    );
                    v___y_3029_ = v___x_3033_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3034_ = leanh::lean_ctor_get_uint64(
                        v_x_3026_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3029_ = v_hash_3034_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3030_ = lean_uint64_to_usize(v___y_3029_);
                v___x_3031_ = 1usize;
                v___x_3032_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_3025_, v___x_3030_, v___x_3031_, v_x_3026_, v_x_3027_);
                return v___x_3032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_eraseCore(
    mut v_d_3035_: *mut leanh::LeanObject,
    mut v_declName_3036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tree_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tree_3037_ = leanh::lean_ctor_get(v_d_3035_, 0);
                v_erased_3038_ = leanh::lean_ctor_get(v_d_3035_, 1);
                v_isSharedCheck_3047_ = (!leanh::lean_is_exclusive(v_d_3035_)) as u8;
                if v_isSharedCheck_3047_ == 0 {
                    v___x_3040_ = v_d_3035_;
                    v_isShared_3041_ = v_isSharedCheck_3047_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_erased_3038_);
                    leanh::lean_inc(v_tree_3037_);
                    leanh::lean_dec(v_d_3035_);
                    v___x_3040_ = leanh::lean_box(0);
                    v_isShared_3041_ = v_isSharedCheck_3047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3042_ = leanh::lean_box(0);
                v___x_3043_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_erased_3038_, v_declName_3036_, v___x_3042_);
                if v_isShared_3041_ == 0 {
                    leanh::lean_ctor_set(v___x_3040_, 1, v___x_3043_);
                    v___x_3045_ = v___x_3040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_tree_3037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3043_);
                    v___x_3045_ = v_reuseFailAlloc_3046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0(
    mut v_00_u03b2_3048_: *mut leanh::LeanObject,
    mut v_x_3049_: *mut leanh::LeanObject,
    mut v_x_3050_: *mut leanh::LeanObject,
    mut v_x_3051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3052_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_x_3049_, v_x_3050_, v_x_3051_);
    return v___x_3052_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(
    mut v_00_u03b2_3053_: *mut leanh::LeanObject,
    mut v_x_3054_: *mut leanh::LeanObject,
    mut v_x_3055_: usize,
    mut v_x_3056_: usize,
    mut v_x_3057_: *mut leanh::LeanObject,
    mut v_x_3058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3059_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_3054_, v_x_3055_, v_x_3056_, v_x_3057_, v_x_3058_);
    return v___x_3059_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___boxed(
    mut v_00_u03b2_3060_: *mut leanh::LeanObject,
    mut v_x_3061_: *mut leanh::LeanObject,
    mut v_x_3062_: *mut leanh::LeanObject,
    mut v_x_3063_: *mut leanh::LeanObject,
    mut v_x_3064_: *mut leanh::LeanObject,
    mut v_x_3065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_576__boxed_3066_: usize = 0;
    let mut v_x_577__boxed_3067_: usize = 0;
    let mut v_res_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_576__boxed_3066_ = leanh::lean_unbox_usize(v_x_3062_);
    leanh::lean_dec(v_x_3062_);
    v_x_577__boxed_3067_ = leanh::lean_unbox_usize(v_x_3063_);
    leanh::lean_dec(v_x_3063_);
    v_res_3068_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(v_00_u03b2_3060_, v_x_3061_, v_x_576__boxed_3066_, v_x_577__boxed_3067_, v_x_3064_, v_x_3065_);
    return v_res_3068_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3069_: *mut leanh::LeanObject,
    mut v_n_3070_: *mut leanh::LeanObject,
    mut v_k_3071_: *mut leanh::LeanObject,
    mut v_v_3072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3073_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v_n_3070_, v_k_3071_, v_v_3072_);
    return v___x_3073_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3074_: *mut leanh::LeanObject,
    mut v_depth_3075_: usize,
    mut v_keys_3076_: *mut leanh::LeanObject,
    mut v_vals_3077_: *mut leanh::LeanObject,
    mut v_heq_3078_: *mut leanh::LeanObject,
    mut v_i_3079_: *mut leanh::LeanObject,
    mut v_entries_3080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_3075_, v_keys_3076_, v_vals_3077_, v_i_3079_, v_entries_3080_);
    return v___x_3081_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_3082_: *mut leanh::LeanObject,
    mut v_depth_3083_: *mut leanh::LeanObject,
    mut v_keys_3084_: *mut leanh::LeanObject,
    mut v_vals_3085_: *mut leanh::LeanObject,
    mut v_heq_3086_: *mut leanh::LeanObject,
    mut v_i_3087_: *mut leanh::LeanObject,
    mut v_entries_3088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3089_: usize = 0;
    let mut v_res_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3089_ = leanh::lean_unbox_usize(v_depth_3083_);
    leanh::lean_dec(v_depth_3083_);
    v_res_3090_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(v_00_u03b2_3082_, v_depth_boxed_3089_, v_keys_3084_, v_vals_3085_, v_heq_3086_, v_i_3087_, v_entries_3088_);
    leanh::lean_dec_ref(v_vals_3085_);
    leanh::lean_dec_ref(v_keys_3084_);
    return v_res_3090_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3091_: *mut leanh::LeanObject,
    mut v_x_3092_: *mut leanh::LeanObject,
    mut v_x_3093_: *mut leanh::LeanObject,
    mut v_x_3094_: *mut leanh::LeanObject,
    mut v_x_3095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3096_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3092_, v_x_3093_, v_x_3094_, v_x_3095_);
    return v___x_3096_;
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(
    mut v_declName_3097_: *mut leanh::LeanObject,
    mut v_x1_3098_: u8,
    mut v_x2_3099_: *mut leanh::LeanObject,
) -> u8 {
    if v_x1_3098_ == 0 {
        let mut v_declName_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3101_: u8 = 0;
        v_declName_3100_ = leanh::lean_ctor_get(v_x2_3099_, 0);
        v___x_3101_ = lean_name_eq(v_declName_3100_, v_declName_3097_);
        return v___x_3101_;
    } else {
        return v_x1_3098_;
    }
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed(
    mut v_declName_3102_: *mut leanh::LeanObject,
    mut v_x1_3103_: *mut leanh::LeanObject,
    mut v_x2_3104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x1_1199__boxed_3105_: u8 = 0;
    let mut v_res_3106_: u8 = 0;
    let mut v_r_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x1_1199__boxed_3105_ = (leanh::lean_unbox(v_x1_3103_) as u8);
    v_res_3106_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(
        v_declName_3102_,
        v_x1_1199__boxed_3105_,
        v_x2_3104_,
    );
    leanh::lean_dec_ref(v_x2_3104_);
    leanh::lean_dec(v_declName_3102_);
    v_r_3107_ = leanh::lean_box((v_res_3106_) as usize);
    return v_r_3107_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(
    mut v_f_3108_: *mut leanh::LeanObject,
    mut v_as_3109_: *mut leanh::LeanObject,
    mut v_i_3110_: usize,
    mut v_stop_3111_: usize,
    mut v_b_3112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: usize = 0;
    let mut v___x_3117_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3113_ = lean_usize_dec_eq(v_i_3110_, v_stop_3111_);
                if v___x_3113_ == 0 {
                    v___x_3114_ = lean_array_uget_borrowed(v_as_3109_, v_i_3110_);
                    leanh::lean_inc(v_f_3108_);
                    leanh::lean_inc(v___x_3114_);
                    v___x_3115_ = leanh::lean_apply_2(v_f_3108_, v_b_3112_, v___x_3114_);
                    v___x_3116_ = 1usize;
                    v___x_3117_ = lean_usize_add(v_i_3110_, v___x_3116_);
                    v_i_3110_ = v___x_3117_;
                    v_b_3112_ = v___x_3115_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_f_3108_);
                    return v_b_3112_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg___boxed(
    mut v_f_3119_: *mut leanh::LeanObject,
    mut v_as_3120_: *mut leanh::LeanObject,
    mut v_i_3121_: *mut leanh::LeanObject,
    mut v_stop_3122_: *mut leanh::LeanObject,
    mut v_b_3123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3124_: usize = 0;
    let mut v_stop_boxed_3125_: usize = 0;
    let mut v_res_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3124_ = leanh::lean_unbox_usize(v_i_3121_);
    leanh::lean_dec(v_i_3121_);
    v_stop_boxed_3125_ = leanh::lean_unbox_usize(v_stop_3122_);
    leanh::lean_dec(v_stop_3122_);
    v_res_3126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_3119_, v_as_3120_, v_i_boxed_3124_, v_stop_boxed_3125_, v_b_3123_);
    leanh::lean_dec_ref(v_as_3120_);
    return v_res_3126_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(
    mut v_f_3127_: *mut leanh::LeanObject,
    mut v_x_3128_: *mut leanh::LeanObject,
    mut v_x_3129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vs_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: u8 = 0;
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3138_: usize = 0;
    let mut v___x_3139_: usize = 0;
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: usize = 0;
    let mut v___x_3142_: usize = 0;
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: u8 = 0;
    let mut v___x_3148_: u8 = 0;
    let mut v___x_3149_: usize = 0;
    let mut v___x_3150_: usize = 0;
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: usize = 0;
    let mut v___x_3153_: usize = 0;
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: u8 = 0;
    let mut v___x_3156_: usize = 0;
    let mut v___x_3157_: usize = 0;
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: usize = 0;
    let mut v___x_3160_: usize = 0;
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_3130_ = leanh::lean_ctor_get(v_x_3129_, 0);
                v_children_3131_ = leanh::lean_ctor_get(v_x_3129_, 1);
                v___x_3132_ = leanh::lean_unsigned_to_nat(0);
                v___x_3144_ = lean_array_get_size(v_vs_3130_);
                v___x_3145_ = lean_nat_dec_lt(v___x_3132_, v___x_3144_);
                if v___x_3145_ == 0 {
                    v___x_3146_ = lean_array_get_size(v_children_3131_);
                    v___x_3147_ = lean_nat_dec_lt(v___x_3132_, v___x_3146_);
                    if v___x_3147_ == 0 {
                        leanh::lean_dec(v_f_3127_);
                        return v_x_3128_;
                    } else {
                        v___x_3148_ = lean_nat_dec_le(v___x_3146_, v___x_3146_);
                        if v___x_3148_ == 0 {
                            if v___x_3147_ == 0 {
                                leanh::lean_dec(v_f_3127_);
                                return v_x_3128_;
                            } else {
                                v___x_3149_ = 0usize;
                                v___x_3150_ = lean_usize_of_nat(v___x_3146_);
                                v___x_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_3127_, v_children_3131_, v___x_3149_, v___x_3150_, v_x_3128_);
                                return v___x_3151_;
                            }
                        } else {
                            v___x_3152_ = 0usize;
                            v___x_3153_ = lean_usize_of_nat(v___x_3146_);
                            v___x_3154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_3127_, v_children_3131_, v___x_3152_, v___x_3153_, v_x_3128_);
                            return v___x_3154_;
                        }
                    }
                } else {
                    v___x_3155_ = lean_nat_dec_le(v___x_3144_, v___x_3144_);
                    if v___x_3155_ == 0 {
                        if v___x_3145_ == 0 {
                            v_s_3134_ = v_x_3128_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3156_ = 0usize;
                            v___x_3157_ = lean_usize_of_nat(v___x_3144_);
                            leanh::lean_inc(v_f_3127_);
                            v___x_3158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_3127_, v_vs_3130_, v___x_3156_, v___x_3157_, v_x_3128_);
                            v_s_3134_ = v___x_3158_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_3159_ = 0usize;
                        v___x_3160_ = lean_usize_of_nat(v___x_3144_);
                        leanh::lean_inc(v_f_3127_);
                        v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_3127_, v_vs_3130_, v___x_3159_, v___x_3160_, v_x_3128_);
                        v_s_3134_ = v___x_3161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3135_ = lean_array_get_size(v_children_3131_);
                v___x_3136_ = lean_nat_dec_lt(v___x_3132_, v___x_3135_);
                if v___x_3136_ == 0 {
                    leanh::lean_dec(v_f_3127_);
                    return v_s_3134_;
                } else {
                    v___x_3137_ = lean_nat_dec_le(v___x_3135_, v___x_3135_);
                    if v___x_3137_ == 0 {
                        if v___x_3136_ == 0 {
                            leanh::lean_dec(v_f_3127_);
                            return v_s_3134_;
                        } else {
                            v___x_3138_ = 0usize;
                            v___x_3139_ = lean_usize_of_nat(v___x_3135_);
                            v___x_3140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_3127_, v_children_3131_, v___x_3138_, v___x_3139_, v_s_3134_);
                            return v___x_3140_;
                        }
                    } else {
                        v___x_3141_ = 0usize;
                        v___x_3142_ = lean_usize_of_nat(v___x_3135_);
                        v___x_3143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_3127_, v_children_3131_, v___x_3141_, v___x_3142_, v_s_3134_);
                        return v___x_3143_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(
    mut v_f_3162_: *mut leanh::LeanObject,
    mut v_as_3163_: *mut leanh::LeanObject,
    mut v_i_3164_: usize,
    mut v_stop_3165_: usize,
    mut v_b_3166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3167_: u8 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: usize = 0;
    let mut v___x_3172_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3167_ = lean_usize_dec_eq(v_i_3164_, v_stop_3165_);
                if v___x_3167_ == 0 {
                    v___x_3168_ = lean_array_uget_borrowed(v_as_3163_, v_i_3164_);
                    v_snd_3169_ = leanh::lean_ctor_get(v___x_3168_, 1);
                    leanh::lean_inc(v_f_3162_);
                    v___x_3170_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_3162_, v_b_3166_, v_snd_3169_);
                    v___x_3171_ = 1usize;
                    v___x_3172_ = lean_usize_add(v_i_3164_, v___x_3171_);
                    v_i_3164_ = v___x_3172_;
                    v_b_3166_ = v___x_3170_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_f_3162_);
                    return v_b_3166_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg___boxed(
    mut v_f_3174_: *mut leanh::LeanObject,
    mut v_as_3175_: *mut leanh::LeanObject,
    mut v_i_3176_: *mut leanh::LeanObject,
    mut v_stop_3177_: *mut leanh::LeanObject,
    mut v_b_3178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3179_: usize = 0;
    let mut v_stop_boxed_3180_: usize = 0;
    let mut v_res_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3179_ = leanh::lean_unbox_usize(v_i_3176_);
    leanh::lean_dec(v_i_3176_);
    v_stop_boxed_3180_ = leanh::lean_unbox_usize(v_stop_3177_);
    leanh::lean_dec(v_stop_3177_);
    v_res_3181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_3174_, v_as_3175_, v_i_boxed_3179_, v_stop_boxed_3180_, v_b_3178_);
    leanh::lean_dec_ref(v_as_3175_);
    return v_res_3181_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg___boxed(
    mut v_f_3182_: *mut leanh::LeanObject,
    mut v_x_3183_: *mut leanh::LeanObject,
    mut v_x_3184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3185_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_3182_, v_x_3183_, v_x_3184_);
    leanh::lean_dec_ref(v_x_3184_);
    return v_res_3185_;
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(
    mut v___f_3186_: *mut leanh::LeanObject,
    mut v_s_3187_: u8,
    mut v_x_3188_: *mut leanh::LeanObject,
    mut v_t_3189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = leanh::lean_box((v_s_3187_) as usize);
    v___x_3191_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v___f_3186_, v___x_3190_, v_t_3189_);
    return v___x_3191_;
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed(
    mut v___f_3192_: *mut leanh::LeanObject,
    mut v_s_3193_: *mut leanh::LeanObject,
    mut v_x_3194_: *mut leanh::LeanObject,
    mut v_t_3195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_3196_: u8 = 0;
    let mut v_res_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_3196_ = (leanh::lean_unbox(v_s_3193_) as u8);
    v_res_3197_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(
        v___f_3192_,
        v_s_boxed_3196_,
        v_x_3194_,
        v_t_3195_,
    );
    leanh::lean_dec_ref(v_t_3195_);
    leanh::lean_dec(v_x_3194_);
    return v_res_3197_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(
    mut v_keys_3198_: *mut leanh::LeanObject,
    mut v_i_3199_: *mut leanh::LeanObject,
    mut v_k_3200_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: u8 = 0;
    let mut v_k_x27_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3201_ = lean_array_get_size(v_keys_3198_);
                v___x_3202_ = lean_nat_dec_lt(v_i_3199_, v___x_3201_);
                if v___x_3202_ == 0 {
                    leanh::lean_dec(v_i_3199_);
                    return v___x_3202_;
                } else {
                    v_k_x27_3203_ = lean_array_fget_borrowed(v_keys_3198_, v_i_3199_);
                    v___x_3204_ = lean_name_eq(v_k_3200_, v_k_x27_3203_);
                    if v___x_3204_ == 0 {
                        v___x_3205_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3206_ = lean_nat_add(v_i_3199_, v___x_3205_);
                        leanh::lean_dec(v_i_3199_);
                        v_i_3199_ = v___x_3206_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_3199_);
                        return v___x_3204_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg___boxed(
    mut v_keys_3208_: *mut leanh::LeanObject,
    mut v_i_3209_: *mut leanh::LeanObject,
    mut v_k_3210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3211_: u8 = 0;
    let mut v_r_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3211_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_3208_, v_i_3209_, v_k_3210_);
    leanh::lean_dec(v_k_3210_);
    leanh::lean_dec_ref(v_keys_3208_);
    v_r_3212_ = leanh::lean_box((v_res_3211_) as usize);
    return v_r_3212_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(
    mut v_x_3213_: *mut leanh::LeanObject,
    mut v_x_3214_: usize,
    mut v_x_3215_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: usize = 0;
    let mut v___x_3219_: usize = 0;
    let mut v___x_3220_: usize = 0;
    let mut v_j_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: u8 = 0;
    let mut v_node_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: usize = 0;
    let mut v___x_3228_: u8 = 0;
    let mut v_ks_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3213_) == 0 {
                    v_es_3216_ = leanh::lean_ctor_get(v_x_3213_, 0);
                    v___x_3217_ = leanh::lean_box(2);
                    v___x_3218_ = 5usize;
                    v___x_3219_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
                    v___x_3220_ = lean_usize_land(v_x_3214_, v___x_3219_);
                    v_j_3221_ = lean_usize_to_nat(v___x_3220_);
                    v___x_3222_ = lean_array_get_borrowed(v___x_3217_, v_es_3216_, v_j_3221_);
                    leanh::lean_dec(v_j_3221_);
                    match leanh::lean_obj_tag(v___x_3222_) {
                        0 => {
                            v_key_3223_ = leanh::lean_ctor_get(v___x_3222_, 0);
                            v___x_3224_ = lean_name_eq(v_x_3215_, v_key_3223_);
                            return v___x_3224_;
                        }
                        1 => {
                            v_node_3225_ = leanh::lean_ctor_get(v___x_3222_, 0);
                            v___x_3226_ = lean_usize_shift_right(v_x_3214_, v___x_3218_);
                            v_x_3213_ = v_node_3225_;
                            v_x_3214_ = v___x_3226_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3228_ = 0;
                            return v___x_3228_;
                        }
                    }
                } else {
                    v_ks_3229_ = leanh::lean_ctor_get(v_x_3213_, 0);
                    v___x_3230_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3231_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_ks_3229_, v___x_3230_, v_x_3215_);
                    return v___x_3231_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg___boxed(
    mut v_x_3232_: *mut leanh::LeanObject,
    mut v_x_3233_: *mut leanh::LeanObject,
    mut v_x_3234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1331__boxed_3235_: usize = 0;
    let mut v_res_3236_: u8 = 0;
    let mut v_r_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1331__boxed_3235_ = leanh::lean_unbox_usize(v_x_3233_);
    leanh::lean_dec(v_x_3233_);
    v_res_3236_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_3232_, v_x_1331__boxed_3235_, v_x_3234_);
    leanh::lean_dec(v_x_3234_);
    leanh::lean_dec_ref(v_x_3232_);
    v_r_3237_ = leanh::lean_box((v_res_3236_) as usize);
    return v_r_3237_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(
    mut v_x_3238_: *mut leanh::LeanObject,
    mut v_x_3239_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_3241_: u64 = 0;
    let mut v___x_3242_: usize = 0;
    let mut v___x_3243_: u8 = 0;
    let mut v___x_3244_: u64 = 0;
    let mut v_hash_3245_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3239_) == 0 {
                    v___x_3244_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once
                        ),
                        _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0,
                    );
                    v___y_3241_ = v___x_3244_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3245_ = leanh::lean_ctor_get_uint64(
                        v_x_3239_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3241_ = v_hash_3245_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3242_ = lean_uint64_to_usize(v___y_3241_);
                v___x_3243_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_3238_, v___x_3242_, v_x_3239_);
                return v___x_3243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg___boxed(
    mut v_x_3246_: *mut leanh::LeanObject,
    mut v_x_3247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3248_: u8 = 0;
    let mut v_r_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3248_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_3246_, v_x_3247_);
    leanh::lean_dec(v_x_3247_);
    leanh::lean_dec_ref(v_x_3246_);
    v_r_3249_ = leanh::lean_box((v_res_3248_) as usize);
    return v_r_3249_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(
    mut v_f_3250_: *mut leanh::LeanObject,
    mut v_keys_3251_: *mut leanh::LeanObject,
    mut v_vals_3252_: *mut leanh::LeanObject,
    mut v_i_3253_: *mut leanh::LeanObject,
    mut v_acc_3254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: u8 = 0;
    let mut v_k_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3255_ = lean_array_get_size(v_keys_3251_);
                v___x_3256_ = lean_nat_dec_lt(v_i_3253_, v___x_3255_);
                if v___x_3256_ == 0 {
                    leanh::lean_dec(v_i_3253_);
                    leanh::lean_dec(v_f_3250_);
                    return v_acc_3254_;
                } else {
                    v_k_3257_ = lean_array_fget_borrowed(v_keys_3251_, v_i_3253_);
                    v_v_3258_ = lean_array_fget_borrowed(v_vals_3252_, v_i_3253_);
                    leanh::lean_inc(v_f_3250_);
                    leanh::lean_inc(v_v_3258_);
                    leanh::lean_inc(v_k_3257_);
                    v___x_3259_ =
                        leanh::lean_apply_3(v_f_3250_, v_acc_3254_, v_k_3257_, v_v_3258_);
                    v___x_3260_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3261_ = lean_nat_add(v_i_3253_, v___x_3260_);
                    leanh::lean_dec(v_i_3253_);
                    v_i_3253_ = v___x_3261_;
                    v_acc_3254_ = v___x_3259_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_f_3263_: *mut leanh::LeanObject,
    mut v_keys_3264_: *mut leanh::LeanObject,
    mut v_vals_3265_: *mut leanh::LeanObject,
    mut v_i_3266_: *mut leanh::LeanObject,
    mut v_acc_3267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3268_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_3263_, v_keys_3264_, v_vals_3265_, v_i_3266_, v_acc_3267_);
    leanh::lean_dec_ref(v_vals_3265_);
    leanh::lean_dec_ref(v_keys_3264_);
    return v_res_3268_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(
    mut v_f_3269_: *mut leanh::LeanObject,
    mut v_x_3270_: *mut leanh::LeanObject,
    mut v_x_3271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3270_) == 0 {
        let mut v_es_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3275_: u8 = 0;
        v_es_3272_ = leanh::lean_ctor_get(v_x_3270_, 0);
        v___x_3273_ = leanh::lean_unsigned_to_nat(0);
        v___x_3274_ = lean_array_get_size(v_es_3272_);
        v___x_3275_ = lean_nat_dec_lt(v___x_3273_, v___x_3274_);
        if v___x_3275_ == 0 {
            leanh::lean_dec(v_f_3269_);
            return v_x_3271_;
        } else {
            let mut v___x_3276_: u8 = 0;
            v___x_3276_ = lean_nat_dec_le(v___x_3274_, v___x_3274_);
            if v___x_3276_ == 0 {
                if v___x_3275_ == 0 {
                    leanh::lean_dec(v_f_3269_);
                    return v_x_3271_;
                } else {
                    let mut v___x_3277_: usize = 0;
                    let mut v___x_3278_: usize = 0;
                    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_3277_ = 0usize;
                    v___x_3278_ = lean_usize_of_nat(v___x_3274_);
                    v___x_3279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_3269_, v_es_3272_, v___x_3277_, v___x_3278_, v_x_3271_);
                    return v___x_3279_;
                }
            } else {
                let mut v___x_3280_: usize = 0;
                let mut v___x_3281_: usize = 0;
                let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3280_ = 0usize;
                v___x_3281_ = lean_usize_of_nat(v___x_3274_);
                v___x_3282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_3269_, v_es_3272_, v___x_3280_, v___x_3281_, v_x_3271_);
                return v___x_3282_;
            }
        }
    } else {
        let mut v_ks_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ks_3283_ = leanh::lean_ctor_get(v_x_3270_, 0);
        v_vs_3284_ = leanh::lean_ctor_get(v_x_3270_, 1);
        v___x_3285_ = leanh::lean_unsigned_to_nat(0);
        v___x_3286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_3269_, v_ks_3283_, v_vs_3284_, v___x_3285_, v_x_3271_);
        return v___x_3286_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(
    mut v_f_3287_: *mut leanh::LeanObject,
    mut v_as_3288_: *mut leanh::LeanObject,
    mut v_i_3289_: usize,
    mut v_stop_3290_: usize,
    mut v_b_3291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: usize = 0;
    let mut v___x_3295_: usize = 0;
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3297_ = lean_usize_dec_eq(v_i_3289_, v_stop_3290_);
                if v___x_3297_ == 0 {
                    v___x_3298_ = lean_array_uget_borrowed(v_as_3288_, v_i_3289_);
                    match leanh::lean_obj_tag(v___x_3298_) {
                        0 => {
                            v_key_3299_ = leanh::lean_ctor_get(v___x_3298_, 0);
                            v_val_3300_ = leanh::lean_ctor_get(v___x_3298_, 1);
                            leanh::lean_inc(v_f_3287_);
                            leanh::lean_inc(v_val_3300_);
                            leanh::lean_inc(v_key_3299_);
                            v___x_3301_ = leanh::lean_apply_3(
                                v_f_3287_,
                                v_b_3291_,
                                v_key_3299_,
                                v_val_3300_,
                            );
                            v___y_3293_ = v___x_3301_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_3302_ = leanh::lean_ctor_get(v___x_3298_, 0);
                            leanh::lean_inc(v_f_3287_);
                            v___x_3303_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_3287_, v_node_3302_, v_b_3291_);
                            v___y_3293_ = v___x_3303_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_3293_ = v_b_3291_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_f_3287_);
                    return v_b_3291_;
                }
            }
            1 => {
                v___x_3294_ = 1usize;
                v___x_3295_ = lean_usize_add(v_i_3289_, v___x_3294_);
                v_i_3289_ = v___x_3295_;
                v_b_3291_ = v___y_3293_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg___boxed(
    mut v_f_3304_: *mut leanh::LeanObject,
    mut v_as_3305_: *mut leanh::LeanObject,
    mut v_i_3306_: *mut leanh::LeanObject,
    mut v_stop_3307_: *mut leanh::LeanObject,
    mut v_b_3308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3309_: usize = 0;
    let mut v_stop_boxed_3310_: usize = 0;
    let mut v_res_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3309_ = leanh::lean_unbox_usize(v_i_3306_);
    leanh::lean_dec(v_i_3306_);
    v_stop_boxed_3310_ = leanh::lean_unbox_usize(v_stop_3307_);
    leanh::lean_dec(v_stop_3307_);
    v_res_3311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_3304_, v_as_3305_, v_i_boxed_3309_, v_stop_boxed_3310_, v_b_3308_);
    leanh::lean_dec_ref(v_as_3305_);
    return v_res_3311_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg___boxed(
    mut v_f_3312_: *mut leanh::LeanObject,
    mut v_x_3313_: *mut leanh::LeanObject,
    mut v_x_3314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_3312_, v_x_3313_, v_x_3314_);
    leanh::lean_dec_ref(v_x_3313_);
    return v_res_3315_;
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_contains(
    mut v_d_3316_: *mut leanh::LeanObject,
    mut v_declName_3317_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_tree_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: u8 = 0;
    v_tree_3318_ = leanh::lean_ctor_get(v_d_3316_, 0);
    v_erased_3319_ = leanh::lean_ctor_get(v_d_3316_, 1);
    leanh::lean_inc(v_declName_3317_);
    v___f_3320_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3320_, 0, v_declName_3317_);
    v___f_3321_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_3321_, 0, v___f_3320_);
    v___x_3322_ = 0;
    v___x_3323_ = leanh::lean_box((v___x_3322_) as usize);
    v___x_3324_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v___f_3321_, v_tree_3318_, v___x_3323_);
    v___x_3325_ = (leanh::lean_unbox(v___x_3324_) as u8);
    if v___x_3325_ == 0 {
        let mut v___x_3326_: u8 = 0;
        leanh::lean_dec(v_declName_3317_);
        v___x_3326_ = (leanh::lean_unbox(v___x_3324_) as u8);
        leanh::lean_dec(v___x_3324_);
        return v___x_3326_;
    } else {
        let mut v___x_3327_: u8 = 0;
        v___x_3327_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_erased_3319_, v_declName_3317_);
        leanh::lean_dec(v_declName_3317_);
        if v___x_3327_ == 0 {
            let mut v___x_3328_: u8 = 0;
            v___x_3328_ = (leanh::lean_unbox(v___x_3324_) as u8);
            leanh::lean_dec(v___x_3324_);
            return v___x_3328_;
        } else {
            leanh::lean_dec(v___x_3324_);
            return v___x_3322_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_contains___boxed(
    mut v_d_3329_: *mut leanh::LeanObject,
    mut v_declName_3330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3331_: u8 = 0;
    let mut v_r_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_3329_, v_declName_3330_);
    leanh::lean_dec_ref(v_d_3329_);
    v_r_3332_ = leanh::lean_box((v_res_3331_) as usize);
    return v_r_3332_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(
    mut v_00_u03c3_3333_: *mut leanh::LeanObject,
    mut v_00_u03b1_3334_: *mut leanh::LeanObject,
    mut v_f_3335_: *mut leanh::LeanObject,
    mut v_x_3336_: *mut leanh::LeanObject,
    mut v_x_3337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3338_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_3335_, v_x_3336_, v_x_3337_);
    return v___x_3338_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___boxed(
    mut v_00_u03c3_3339_: *mut leanh::LeanObject,
    mut v_00_u03b1_3340_: *mut leanh::LeanObject,
    mut v_f_3341_: *mut leanh::LeanObject,
    mut v_x_3342_: *mut leanh::LeanObject,
    mut v_x_3343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3344_ =
        l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(
            v_00_u03c3_3339_,
            v_00_u03b1_3340_,
            v_f_3341_,
            v_x_3342_,
            v_x_3343_,
        );
    leanh::lean_dec_ref(v_x_3343_);
    return v_res_3344_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(
    mut v_map_3345_: *mut leanh::LeanObject,
    mut v_f_3346_: *mut leanh::LeanObject,
    mut v_init_3347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3348_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_3346_, v_map_3345_, v_init_3347_);
    return v___x_3348_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg___boxed(
    mut v_map_3349_: *mut leanh::LeanObject,
    mut v_f_3350_: *mut leanh::LeanObject,
    mut v_init_3351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3352_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(v_map_3349_, v_f_3350_, v_init_3351_);
    leanh::lean_dec_ref(v_map_3349_);
    return v_res_3352_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(
    mut v_00_u03c3_3353_: *mut leanh::LeanObject,
    mut v_00_u03b2_3354_: *mut leanh::LeanObject,
    mut v_map_3355_: *mut leanh::LeanObject,
    mut v_f_3356_: *mut leanh::LeanObject,
    mut v_init_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3358_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_3356_, v_map_3355_, v_init_3357_);
    return v___x_3358_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___boxed(
    mut v_00_u03c3_3359_: *mut leanh::LeanObject,
    mut v_00_u03b2_3360_: *mut leanh::LeanObject,
    mut v_map_3361_: *mut leanh::LeanObject,
    mut v_f_3362_: *mut leanh::LeanObject,
    mut v_init_3363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3364_ =
        l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(
            v_00_u03c3_3359_,
            v_00_u03b2_3360_,
            v_map_3361_,
            v_f_3362_,
            v_init_3363_,
        );
    leanh::lean_dec_ref(v_map_3361_);
    return v_res_3364_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(
    mut v_00_u03b2_3365_: *mut leanh::LeanObject,
    mut v_x_3366_: *mut leanh::LeanObject,
    mut v_x_3367_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3368_: u8 = 0;
    v___x_3368_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_3366_, v_x_3367_);
    return v___x_3368_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___boxed(
    mut v_00_u03b2_3369_: *mut leanh::LeanObject,
    mut v_x_3370_: *mut leanh::LeanObject,
    mut v_x_3371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3372_: u8 = 0;
    let mut v_r_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3372_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(
            v_00_u03b2_3369_,
            v_x_3370_,
            v_x_3371_,
        );
    leanh::lean_dec(v_x_3371_);
    leanh::lean_dec_ref(v_x_3370_);
    v_r_3373_ = leanh::lean_box((v_res_3372_) as usize);
    return v_r_3373_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(
    mut v_00_u03b1_3374_: *mut leanh::LeanObject,
    mut v_00_u03c3_3375_: *mut leanh::LeanObject,
    mut v_f_3376_: *mut leanh::LeanObject,
    mut v_as_3377_: *mut leanh::LeanObject,
    mut v_i_3378_: usize,
    mut v_stop_3379_: usize,
    mut v_b_3380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_3376_, v_as_3377_, v_i_3378_, v_stop_3379_, v_b_3380_);
    return v___x_3381_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___boxed(
    mut v_00_u03b1_3382_: *mut leanh::LeanObject,
    mut v_00_u03c3_3383_: *mut leanh::LeanObject,
    mut v_f_3384_: *mut leanh::LeanObject,
    mut v_as_3385_: *mut leanh::LeanObject,
    mut v_i_3386_: *mut leanh::LeanObject,
    mut v_stop_3387_: *mut leanh::LeanObject,
    mut v_b_3388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3389_: usize = 0;
    let mut v_stop_boxed_3390_: usize = 0;
    let mut v_res_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3389_ = leanh::lean_unbox_usize(v_i_3386_);
    leanh::lean_dec(v_i_3386_);
    v_stop_boxed_3390_ = leanh::lean_unbox_usize(v_stop_3387_);
    leanh::lean_dec(v_stop_3387_);
    v_res_3391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(v_00_u03b1_3382_, v_00_u03c3_3383_, v_f_3384_, v_as_3385_, v_i_boxed_3389_, v_stop_boxed_3390_, v_b_3388_);
    leanh::lean_dec_ref(v_as_3385_);
    return v_res_3391_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(
    mut v_00_u03b1_3392_: *mut leanh::LeanObject,
    mut v_00_u03c3_3393_: *mut leanh::LeanObject,
    mut v_f_3394_: *mut leanh::LeanObject,
    mut v_as_3395_: *mut leanh::LeanObject,
    mut v_i_3396_: usize,
    mut v_stop_3397_: usize,
    mut v_b_3398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_3394_, v_as_3395_, v_i_3396_, v_stop_3397_, v_b_3398_);
    return v___x_3399_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___boxed(
    mut v_00_u03b1_3400_: *mut leanh::LeanObject,
    mut v_00_u03c3_3401_: *mut leanh::LeanObject,
    mut v_f_3402_: *mut leanh::LeanObject,
    mut v_as_3403_: *mut leanh::LeanObject,
    mut v_i_3404_: *mut leanh::LeanObject,
    mut v_stop_3405_: *mut leanh::LeanObject,
    mut v_b_3406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3407_: usize = 0;
    let mut v_stop_boxed_3408_: usize = 0;
    let mut v_res_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3407_ = leanh::lean_unbox_usize(v_i_3404_);
    leanh::lean_dec(v_i_3404_);
    v_stop_boxed_3408_ = leanh::lean_unbox_usize(v_stop_3405_);
    leanh::lean_dec(v_stop_3405_);
    v_res_3409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(v_00_u03b1_3400_, v_00_u03c3_3401_, v_f_3402_, v_as_3403_, v_i_boxed_3407_, v_stop_boxed_3408_, v_b_3406_);
    leanh::lean_dec_ref(v_as_3403_);
    return v_res_3409_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(
    mut v_00_u03c3_3410_: *mut leanh::LeanObject,
    mut v_00_u03b1_3411_: *mut leanh::LeanObject,
    mut v_00_u03b2_3412_: *mut leanh::LeanObject,
    mut v_f_3413_: *mut leanh::LeanObject,
    mut v_x_3414_: *mut leanh::LeanObject,
    mut v_x_3415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3416_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_3413_, v_x_3414_, v_x_3415_);
    return v___x_3416_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___boxed(
    mut v_00_u03c3_3417_: *mut leanh::LeanObject,
    mut v_00_u03b1_3418_: *mut leanh::LeanObject,
    mut v_00_u03b2_3419_: *mut leanh::LeanObject,
    mut v_f_3420_: *mut leanh::LeanObject,
    mut v_x_3421_: *mut leanh::LeanObject,
    mut v_x_3422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3423_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(v_00_u03c3_3417_, v_00_u03b1_3418_, v_00_u03b2_3419_, v_f_3420_, v_x_3421_, v_x_3422_);
    leanh::lean_dec_ref(v_x_3421_);
    return v_res_3423_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(
    mut v_00_u03b2_3424_: *mut leanh::LeanObject,
    mut v_x_3425_: *mut leanh::LeanObject,
    mut v_x_3426_: usize,
    mut v_x_3427_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3428_: u8 = 0;
    v___x_3428_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_3425_, v_x_3426_, v_x_3427_);
    return v___x_3428_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___boxed(
    mut v_00_u03b2_3429_: *mut leanh::LeanObject,
    mut v_x_3430_: *mut leanh::LeanObject,
    mut v_x_3431_: *mut leanh::LeanObject,
    mut v_x_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1515__boxed_3433_: usize = 0;
    let mut v_res_3434_: u8 = 0;
    let mut v_r_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1515__boxed_3433_ = leanh::lean_unbox_usize(v_x_3431_);
    leanh::lean_dec(v_x_3431_);
    v_res_3434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(v_00_u03b2_3429_, v_x_3430_, v_x_1515__boxed_3433_, v_x_3432_);
    leanh::lean_dec(v_x_3432_);
    leanh::lean_dec_ref(v_x_3430_);
    v_r_3435_ = leanh::lean_box((v_res_3434_) as usize);
    return v_r_3435_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(
    mut v_00_u03b1_3436_: *mut leanh::LeanObject,
    mut v_00_u03b2_3437_: *mut leanh::LeanObject,
    mut v_00_u03c3_3438_: *mut leanh::LeanObject,
    mut v_f_3439_: *mut leanh::LeanObject,
    mut v_as_3440_: *mut leanh::LeanObject,
    mut v_i_3441_: usize,
    mut v_stop_3442_: usize,
    mut v_b_3443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_3439_, v_as_3440_, v_i_3441_, v_stop_3442_, v_b_3443_);
    return v___x_3444_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___boxed(
    mut v_00_u03b1_3445_: *mut leanh::LeanObject,
    mut v_00_u03b2_3446_: *mut leanh::LeanObject,
    mut v_00_u03c3_3447_: *mut leanh::LeanObject,
    mut v_f_3448_: *mut leanh::LeanObject,
    mut v_as_3449_: *mut leanh::LeanObject,
    mut v_i_3450_: *mut leanh::LeanObject,
    mut v_stop_3451_: *mut leanh::LeanObject,
    mut v_b_3452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3453_: usize = 0;
    let mut v_stop_boxed_3454_: usize = 0;
    let mut v_res_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3453_ = leanh::lean_unbox_usize(v_i_3450_);
    leanh::lean_dec(v_i_3450_);
    v_stop_boxed_3454_ = leanh::lean_unbox_usize(v_stop_3451_);
    leanh::lean_dec(v_stop_3451_);
    v_res_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(v_00_u03b1_3445_, v_00_u03b2_3446_, v_00_u03c3_3447_, v_f_3448_, v_as_3449_, v_i_boxed_3453_, v_stop_boxed_3454_, v_b_3452_);
    leanh::lean_dec_ref(v_as_3449_);
    return v_res_3455_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(
    mut v_00_u03c3_3456_: *mut leanh::LeanObject,
    mut v_00_u03b1_3457_: *mut leanh::LeanObject,
    mut v_00_u03b2_3458_: *mut leanh::LeanObject,
    mut v_f_3459_: *mut leanh::LeanObject,
    mut v_keys_3460_: *mut leanh::LeanObject,
    mut v_vals_3461_: *mut leanh::LeanObject,
    mut v_heq_3462_: *mut leanh::LeanObject,
    mut v_i_3463_: *mut leanh::LeanObject,
    mut v_acc_3464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3465_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_3459_, v_keys_3460_, v_vals_3461_, v_i_3463_, v_acc_3464_);
    return v___x_3465_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03c3_3466_: *mut leanh::LeanObject,
    mut v_00_u03b1_3467_: *mut leanh::LeanObject,
    mut v_00_u03b2_3468_: *mut leanh::LeanObject,
    mut v_f_3469_: *mut leanh::LeanObject,
    mut v_keys_3470_: *mut leanh::LeanObject,
    mut v_vals_3471_: *mut leanh::LeanObject,
    mut v_heq_3472_: *mut leanh::LeanObject,
    mut v_i_3473_: *mut leanh::LeanObject,
    mut v_acc_3474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(v_00_u03c3_3466_, v_00_u03b1_3467_, v_00_u03b2_3468_, v_f_3469_, v_keys_3470_, v_vals_3471_, v_heq_3472_, v_i_3473_, v_acc_3474_);
    leanh::lean_dec_ref(v_vals_3471_);
    leanh::lean_dec_ref(v_keys_3470_);
    return v_res_3475_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(
    mut v_00_u03b2_3476_: *mut leanh::LeanObject,
    mut v_keys_3477_: *mut leanh::LeanObject,
    mut v_vals_3478_: *mut leanh::LeanObject,
    mut v_heq_3479_: *mut leanh::LeanObject,
    mut v_i_3480_: *mut leanh::LeanObject,
    mut v_k_3481_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3482_: u8 = 0;
    v___x_3482_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_3477_, v_i_3480_, v_k_3481_);
    return v___x_3482_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___boxed(
    mut v_00_u03b2_3483_: *mut leanh::LeanObject,
    mut v_keys_3484_: *mut leanh::LeanObject,
    mut v_vals_3485_: *mut leanh::LeanObject,
    mut v_heq_3486_: *mut leanh::LeanObject,
    mut v_i_3487_: *mut leanh::LeanObject,
    mut v_k_3488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3489_: u8 = 0;
    let mut v_r_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3489_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(v_00_u03b2_3483_, v_keys_3484_, v_vals_3485_, v_heq_3486_, v_i_3487_, v_k_3488_);
    leanh::lean_dec(v_k_3488_);
    leanh::lean_dec_ref(v_vals_3485_);
    leanh::lean_dec_ref(v_keys_3484_);
    v_r_3490_ = leanh::lean_box((v_res_3489_) as usize);
    return v_r_3490_;
}
pub unsafe fn l_Lean_Meta_Ext_isExtTheorem___redArg(
    mut v_declName_3491_: *mut leanh::LeanObject,
    mut v_a_3492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3494_ = lean_st_ref_get(v_a_3492_);
    v_env_3495_ = leanh::lean_ctor_get(v___x_3494_, 0);
    leanh::lean_inc_ref(v_env_3495_);
    leanh::lean_dec(v___x_3494_);
    v___x_3496_ = l_Lean_Meta_Ext_extExtension;
    v_ext_3497_ = leanh::lean_ctor_get(v___x_3496_, 1);
    v_toEnvExtension_3498_ = leanh::lean_ctor_get(v_ext_3497_, 0);
    v_asyncMode_3499_ = leanh::lean_ctor_get(v_toEnvExtension_3498_, 2);
    v___x_3500_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
    v___x_3501_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_3500_,
        v___x_3496_,
        v_env_3495_,
        v_asyncMode_3499_,
    );
    v___x_3502_ = l_Lean_Meta_Ext_ExtTheorems_contains(v___x_3501_, v_declName_3491_);
    leanh::lean_dec(v___x_3501_);
    v___x_3503_ = leanh::lean_box((v___x_3502_) as usize);
    v___x_3504_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3504_, 0, v___x_3503_);
    return v___x_3504_;
}
pub unsafe fn l_Lean_Meta_Ext_isExtTheorem___redArg___boxed(
    mut v_declName_3505_: *mut leanh::LeanObject,
    mut v_a_3506_: *mut leanh::LeanObject,
    mut v_a_3507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3508_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_3505_, v_a_3506_);
    leanh::lean_dec(v_a_3506_);
    return v_res_3508_;
}
pub unsafe fn l_Lean_Meta_Ext_isExtTheorem(
    mut v_declName_3509_: *mut leanh::LeanObject,
    mut v_a_3510_: *mut leanh::LeanObject,
    mut v_a_3511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3513_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_3509_, v_a_3511_);
    return v___x_3513_;
}
pub unsafe fn l_Lean_Meta_Ext_isExtTheorem___boxed(
    mut v_declName_3514_: *mut leanh::LeanObject,
    mut v_a_3515_: *mut leanh::LeanObject,
    mut v_a_3516_: *mut leanh::LeanObject,
    mut v_a_3517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3518_ = l_Lean_Meta_Ext_isExtTheorem(v_declName_3514_, v_a_3515_, v_a_3516_);
    leanh::lean_dec(v_a_3516_);
    leanh::lean_dec_ref(v_a_3515_);
    return v_res_3518_;
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(
    mut v_d_3519_: *mut leanh::LeanObject,
    mut v_declName_3520_: *mut leanh::LeanObject,
    mut v_toPure_3521_: *mut leanh::LeanObject,
    mut v_____r_3522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3523_ = l_Lean_Meta_Ext_ExtTheorems_eraseCore(v_d_3519_, v_declName_3520_);
    v___x_3524_ =
        leanh::lean_apply_2(v_toPure_3521_, leanh::lean_box(0), v___x_3523_);
    return v___x_3524_;
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1(
    mut v___f_3525_: *mut leanh::LeanObject,
    mut v_____r_3526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3527_ = leanh::lean_apply_1(v___f_3525_, v_____r_3526_);
    return v___x_3527_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3529_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0;
    v___x_3530_ = l_Lean_stringToMessageData(v___x_3529_);
    return v___x_3530_;
}
pub unsafe fn _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3532_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2;
    v___x_3533_ = l_Lean_stringToMessageData(v___x_3532_);
    return v___x_3533_;
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_erase___redArg(
    mut v_inst_3534_: *mut leanh::LeanObject,
    mut v_inst_3535_: *mut leanh::LeanObject,
    mut v_d_3536_: *mut leanh::LeanObject,
    mut v_declName_3537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: u8 = 0;
    v_toApplicative_3538_ = leanh::lean_ctor_get(v_inst_3534_, 0);
    v_toBind_3539_ = leanh::lean_ctor_get(v_inst_3534_, 1);
    leanh::lean_inc(v_toBind_3539_);
    v_toPure_3540_ = leanh::lean_ctor_get(v_toApplicative_3538_, 1);
    leanh::lean_inc(v_toPure_3540_);
    leanh::lean_inc_n(v_declName_3537_, 2);
    leanh::lean_inc_ref(v_d_3536_);
    v___f_3541_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3541_, 0, v_d_3536_);
    leanh::lean_closure_set(v___f_3541_, 1, v_declName_3537_);
    leanh::lean_closure_set(v___f_3541_, 2, v_toPure_3540_);
    v___x_3542_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_3536_, v_declName_3537_);
    if v___x_3542_ == 0 {
        let mut v___f_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_d_3536_);
        v___f_3543_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_3543_, 0, v___f_3541_);
        v___x_3544_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1_once),
            _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1,
        );
        v___x_3545_ = l_Lean_MessageData_ofConstName(v_declName_3537_, v___x_3542_);
        v___x_3546_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3546_, 0, v___x_3544_);
        leanh::lean_ctor_set(v___x_3546_, 1, v___x_3545_);
        v___x_3547_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3_once),
            _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3,
        );
        v___x_3548_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3548_, 0, v___x_3546_);
        leanh::lean_ctor_set(v___x_3548_, 1, v___x_3547_);
        v___x_3549_ = l_Lean_throwError___redArg(v_inst_3534_, v_inst_3535_, v___x_3548_);
        v___x_3550_ = leanh::lean_apply_4(
            v_toBind_3539_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3549_,
            v___f_3543_,
        );
        return v___x_3550_;
    } else {
        let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_3540_);
        leanh::lean_dec_ref(v___f_3541_);
        leanh::lean_dec(v_toBind_3539_);
        leanh::lean_dec_ref(v_inst_3535_);
        leanh::lean_dec_ref(v_inst_3534_);
        v___x_3551_ = leanh::lean_box(0);
        v___x_3552_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(
            v_d_3536_,
            v_declName_3537_,
            v_toPure_3540_,
            v___x_3551_,
        );
        return v___x_3552_;
    }
}
pub unsafe fn l_Lean_Meta_Ext_ExtTheorems_erase(
    mut v_m_3553_: *mut leanh::LeanObject,
    mut v_inst_3554_: *mut leanh::LeanObject,
    mut v_inst_3555_: *mut leanh::LeanObject,
    mut v_d_3556_: *mut leanh::LeanObject,
    mut v_declName_3557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg(
        v_inst_3554_,
        v_inst_3555_,
        v_d_3556_,
        v_declName_3557_,
    );
    return v___x_3558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Ext(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_InsertionSort(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Ext_instInhabitedExtTheorems_default =
        _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Ext_instInhabitedExtTheorems_default);
    l_Lean_Meta_Ext_instInhabitedExtTheorems = _init_l_Lean_Meta_Ext_instInhabitedExtTheorems();
    leanh::lean_mark_persistent(l_Lean_Meta_Ext_instInhabitedExtTheorems);
    res = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Ext_extExtension = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Ext_extExtension);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Ext(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Ext(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_InsertionSort(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_DiscrTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Ext(builtin);
}
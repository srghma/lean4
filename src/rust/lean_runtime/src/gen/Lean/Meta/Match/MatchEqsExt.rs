// Lean compiler output
// Module: Lean.Meta.Match.MatchEqsExt
// Imports: Lean.Meta.Match.Basic Lean.Meta.Match.MatcherInfo Lean.Meta.Eqns
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::lean_erase_macro_scopes;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Meta::Eqns::{
    initialize_Lean_Meta_Eqns, l_Lean_Meta_isEqnLikeSuffix, runtime_initialize_Lean_Meta_Eqns,
};
use crate::r#gen::Lean::Meta::Match::Basic::{
    initialize_Lean_Meta_Match_Basic, runtime_initialize_Lean_Meta_Match_Basic,
};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    initialize_Lean_Meta_Match_MatcherInfo, l_Lean_Meta_Match_instInhabitedMatcherInfo_default,
    l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg,
    runtime_initialize_Lean_Meta_Match_MatcherInfo,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::lean_imports_rs::Lean::Meta::Match::MatchEqsExt::{
    lean_get_congr_match_equations_for, lean_get_match_equations_for,
};
pub static l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__0_value:
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
static mut l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedMatchEqns_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedMatchEqns: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__1_value:
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
    m_data: [101, 113, 110, 78, 97, 109, 101, 115, 0],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__2_value:
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
        l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5_value:
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
        l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [115, 112, 108, 105, 116, 116, 101, 114, 78, 97, 109, 101, 0],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__9_value:
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
        l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__11_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        115, 112, 108, 105, 116, 116, 101, 114, 77, 97, 116, 99, 104, 73, 110, 102, 111, 0,
    ],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__12_value:
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
        l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__11_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__14_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__17_value:
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
        l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__18_value:
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
        l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__14_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Match_instReprMatchEqns___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Match_instReprMatchEqns_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Match_instReprMatchEqns___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Match_instReprMatchEqns: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_instReprMatchEqns___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Match_instInhabitedMatchEqnsExtState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Match_isMatchEqnTheorem___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 3,
        },
        m_objs: [1 as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Meta_Match_isMatchEqnTheorem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_isMatchEqnTheorem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
    v___x_659_ = crate::leanh::lean_box(0);
    v___x_660_ = l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__0;
    v___x_661_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_661_, 0, v___x_660_);
    crate::leanh::lean_ctor_set(v___x_661_, 1, v___x_659_);
    crate::leanh::lean_ctor_set(v___x_661_, 2, v___x_658_);
    return v___x_661_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatchEqns_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1_once),
        _init_l_Lean_Meta_Match_instInhabitedMatchEqns_default___closed__1,
    );
    return v___x_662_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatchEqns() -> *mut crate::leanh::LeanObject {
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_663_ = l_Lean_Meta_Match_instInhabitedMatchEqns_default;
    return v___x_663_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__1(
    mut v_a_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_665_ = lean_nat_to_int(v_a_664_);
    return v___x_665_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_666_: *mut crate::leanh::LeanObject,
    mut v_x_667_: *mut crate::leanh::LeanObject,
    mut v_x_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_668_) == 0 {
                    crate::leanh::lean_dec(v_x_666_);
                    return v_x_667_;
                } else {
                    v_head_669_ = crate::leanh::lean_ctor_get(v_x_668_, 0);
                    v_tail_670_ = crate::leanh::lean_ctor_get(v_x_668_, 1);
                    v_isSharedCheck_681_ = (!crate::leanh::lean_is_exclusive(v_x_668_)) as u8;
                    if v_isSharedCheck_681_ == 0 {
                        v___x_672_ = v_x_668_;
                        v_isShared_673_ = v_isSharedCheck_681_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_670_);
                        crate::leanh::lean_inc(v_head_669_);
                        crate::leanh::lean_dec(v_x_668_);
                        v___x_672_ = crate::leanh::lean_box(0);
                        v_isShared_673_ = v_isSharedCheck_681_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_666_);
                if v_isShared_673_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_672_, 5);
                    crate::leanh::lean_ctor_set(v___x_672_, 1, v_x_666_);
                    crate::leanh::lean_ctor_set(v___x_672_, 0, v_x_667_);
                    v___x_675_ = v___x_672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_680_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_680_, 0, v_x_667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_680_, 1, v_x_666_);
                    v___x_675_ = v_reuseFailAlloc_680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_676_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_677_ = l_Lean_Name_reprPrec(v_head_669_, v___x_676_);
                v___x_678_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_678_, 0, v___x_675_);
                crate::leanh::lean_ctor_set(v___x_678_, 1, v___x_677_);
                v_x_667_ = v___x_678_;
                v_x_668_ = v_tail_670_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2(
    mut v_x_682_: *mut crate::leanh::LeanObject,
    mut v_x_683_: *mut crate::leanh::LeanObject,
    mut v_x_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_689_: u8 = 0;
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_684_) == 0 {
                    crate::leanh::lean_dec(v_x_682_);
                    return v_x_683_;
                } else {
                    v_head_685_ = crate::leanh::lean_ctor_get(v_x_684_, 0);
                    v_tail_686_ = crate::leanh::lean_ctor_get(v_x_684_, 1);
                    v_isSharedCheck_697_ = (!crate::leanh::lean_is_exclusive(v_x_684_)) as u8;
                    if v_isSharedCheck_697_ == 0 {
                        v___x_688_ = v_x_684_;
                        v_isShared_689_ = v_isSharedCheck_697_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_686_);
                        crate::leanh::lean_inc(v_head_685_);
                        crate::leanh::lean_dec(v_x_684_);
                        v___x_688_ = crate::leanh::lean_box(0);
                        v_isShared_689_ = v_isSharedCheck_697_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_682_);
                if v_isShared_689_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_688_, 5);
                    crate::leanh::lean_ctor_set(v___x_688_, 1, v_x_682_);
                    crate::leanh::lean_ctor_set(v___x_688_, 0, v_x_683_);
                    v___x_691_ = v___x_688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_696_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_696_, 0, v_x_683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_696_, 1, v_x_682_);
                    v___x_691_ = v_reuseFailAlloc_696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_692_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_693_ = l_Lean_Name_reprPrec(v_head_685_, v___x_692_);
                v___x_694_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_694_, 0, v___x_691_);
                crate::leanh::lean_ctor_set(v___x_694_, 1, v___x_693_);
                v___x_695_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2_spec__3(v_x_682_, v___x_694_, v_tail_686_);
                return v___x_695_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0___lam__0(
    mut v___y_698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_700_ = l_Lean_Name_reprPrec(v___y_698_, v___x_699_);
    return v___x_700_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0(
    mut v_x_701_: *mut crate::leanh::LeanObject,
    mut v_x_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_701_) == 0 {
        let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_702_);
        v___x_703_ = crate::leanh::lean_box(0);
        return v___x_703_;
    } else {
        let mut v_tail_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_704_ = crate::leanh::lean_ctor_get(v_x_701_, 1);
        if crate::leanh::lean_obj_tag(v_tail_704_) == 0 {
            let mut v_head_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_702_);
            v_head_705_ = crate::leanh::lean_ctor_get(v_x_701_, 0);
            crate::leanh::lean_inc(v_head_705_);
            crate::leanh::lean_dec_ref_known(v_x_701_, 2);
            v___x_706_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0___lam__0(v_head_705_);
            return v___x_706_;
        } else {
            let mut v_head_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_704_);
            v_head_707_ = crate::leanh::lean_ctor_get(v_x_701_, 0);
            crate::leanh::lean_inc(v_head_707_);
            crate::leanh::lean_dec_ref_known(v_x_701_, 2);
            v___x_708_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0___lam__0(v_head_707_);
            v___x_709_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0_spec__2(v_x_702_, v___x_708_, v_tail_704_);
            return v___x_709_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_718_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__0;
    v___x_719_ = lean_string_length(v___x_718_);
    return v___x_719_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5_once
        ),
        _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__5,
    );
    v___x_721_ = lean_nat_to_int(v___x_720_);
    return v___x_721_;
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0(
    mut v_xs_729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: u8 = 0;
    v___x_730_ = lean_array_get_size(v_xs_729_);
    v___x_731_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_732_ = lean_nat_dec_eq(v___x_730_, v___x_731_);
    if v___x_732_ == 0 {
        let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_733_ = lean_array_to_list(v_xs_729_);
        v___x_734_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__3;
        v___x_735_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0_spec__0(v___x_733_, v___x_734_);
        v___x_736_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__6);
        v___x_737_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__7;
        v___x_738_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_738_, 0, v___x_737_);
        crate::leanh::lean_ctor_set(v___x_738_, 1, v___x_735_);
        v___x_739_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__8;
        v___x_740_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_740_, 0, v___x_738_);
        crate::leanh::lean_ctor_set(v___x_740_, 1, v___x_739_);
        v___x_741_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_741_, 0, v___x_736_);
        crate::leanh::lean_ctor_set(v___x_741_, 1, v___x_740_);
        v___x_742_ = l_Std_Format_fill(v___x_741_);
        return v___x_742_;
    } else {
        let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_729_);
        v___x_743_ =
            l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__10;
        return v___x_743_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_757_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_758_ = lean_nat_to_int(v___x_757_);
    return v___x_758_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_762_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_763_ = lean_nat_to_int(v___x_762_);
    return v___x_763_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_767_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_768_ = lean_nat_to_int(v___x_767_);
    return v___x_768_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_770_ = l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__0;
    v___x_771_ = lean_string_length(v___x_770_);
    return v___x_771_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_772_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15_once
        ),
        _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__15,
    );
    v___x_773_ = lean_nat_to_int(v___x_772_);
    return v___x_773_;
}
pub unsafe fn l_Lean_Meta_Match_instReprMatchEqns_repr___redArg(
    mut v_x_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eqnNames_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitterName_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitterMatchInfo_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: u8 = 0;
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_eqnNames_779_ = crate::leanh::lean_ctor_get(v_x_778_, 0);
    crate::leanh::lean_inc_ref(v_eqnNames_779_);
    v_splitterName_780_ = crate::leanh::lean_ctor_get(v_x_778_, 1);
    crate::leanh::lean_inc(v_splitterName_780_);
    v_splitterMatchInfo_781_ = crate::leanh::lean_ctor_get(v_x_778_, 2);
    crate::leanh::lean_inc_ref(v_splitterMatchInfo_781_);
    crate::leanh::lean_dec_ref(v_x_778_);
    v___x_782_ = l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__5;
    v___x_783_ = l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__6;
    v___x_784_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__7,
    );
    v___x_785_ =
        l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0(v_eqnNames_779_);
    v___x_786_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_786_, 0, v___x_784_);
    crate::leanh::lean_ctor_set(v___x_786_, 1, v___x_785_);
    v___x_787_ = 0;
    v___x_788_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_788_, 0, v___x_786_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_788_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_787_,
    );
    v___x_789_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_789_, 0, v___x_783_);
    crate::leanh::lean_ctor_set(v___x_789_, 1, v___x_788_);
    v___x_790_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatchEqns_repr_spec__0___closed__2;
    v___x_791_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_791_, 0, v___x_789_);
    crate::leanh::lean_ctor_set(v___x_791_, 1, v___x_790_);
    v___x_792_ = crate::leanh::lean_box(1);
    v___x_793_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_793_, 0, v___x_791_);
    crate::leanh::lean_ctor_set(v___x_793_, 1, v___x_792_);
    v___x_794_ = l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__9;
    v___x_795_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_795_, 0, v___x_793_);
    crate::leanh::lean_ctor_set(v___x_795_, 1, v___x_794_);
    v___x_796_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_796_, 0, v___x_795_);
    crate::leanh::lean_ctor_set(v___x_796_, 1, v___x_782_);
    v___x_797_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__10,
    );
    v___x_798_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_799_ = l_Lean_Name_reprPrec(v_splitterName_780_, v___x_798_);
    v___x_800_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_800_, 0, v___x_797_);
    crate::leanh::lean_ctor_set(v___x_800_, 1, v___x_799_);
    v___x_801_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_801_, 0, v___x_800_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_801_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_787_,
    );
    v___x_802_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_802_, 0, v___x_796_);
    crate::leanh::lean_ctor_set(v___x_802_, 1, v___x_801_);
    v___x_803_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_803_, 0, v___x_802_);
    crate::leanh::lean_ctor_set(v___x_803_, 1, v___x_790_);
    v___x_804_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_804_, 0, v___x_803_);
    crate::leanh::lean_ctor_set(v___x_804_, 1, v___x_792_);
    v___x_805_ = l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__12;
    v___x_806_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_806_, 0, v___x_804_);
    crate::leanh::lean_ctor_set(v___x_806_, 1, v___x_805_);
    v___x_807_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_807_, 0, v___x_806_);
    crate::leanh::lean_ctor_set(v___x_807_, 1, v___x_782_);
    v___x_808_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13_once
        ),
        _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__13,
    );
    v___x_809_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(v_splitterMatchInfo_781_);
    v___x_810_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_810_, 0, v___x_808_);
    crate::leanh::lean_ctor_set(v___x_810_, 1, v___x_809_);
    v___x_811_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_811_, 0, v___x_810_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_811_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_787_,
    );
    v___x_812_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_812_, 0, v___x_807_);
    crate::leanh::lean_ctor_set(v___x_812_, 1, v___x_811_);
    v___x_813_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16_once
        ),
        _init_l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__16,
    );
    v___x_814_ = l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__17;
    v___x_815_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_815_, 0, v___x_814_);
    crate::leanh::lean_ctor_set(v___x_815_, 1, v___x_812_);
    v___x_816_ = l_Lean_Meta_Match_instReprMatchEqns_repr___redArg___closed__18;
    v___x_817_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_817_, 0, v___x_815_);
    crate::leanh::lean_ctor_set(v___x_817_, 1, v___x_816_);
    v___x_818_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_818_, 0, v___x_813_);
    crate::leanh::lean_ctor_set(v___x_818_, 1, v___x_817_);
    v___x_819_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_819_, 0, v___x_818_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_819_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_787_,
    );
    return v___x_819_;
}
pub unsafe fn l_Lean_Meta_Match_instReprMatchEqns_repr(
    mut v_x_820_: *mut crate::leanh::LeanObject,
    mut v_prec_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_822_ = l_Lean_Meta_Match_instReprMatchEqns_repr___redArg(v_x_820_);
    return v___x_822_;
}
pub unsafe fn l_Lean_Meta_Match_instReprMatchEqns_repr___boxed(
    mut v_x_823_: *mut crate::leanh::LeanObject,
    mut v_prec_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_825_ = l_Lean_Meta_Match_instReprMatchEqns_repr(v_x_823_, v_prec_824_);
    crate::leanh::lean_dec(v_prec_824_);
    return v_res_825_;
}
pub unsafe fn l_Lean_Meta_Match_MatchEqns_size(
    mut v_e_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eqnNames_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_eqnNames_829_ = crate::leanh::lean_ctor_get(v_e_828_, 0);
    v___x_830_ = lean_array_get_size(v_eqnNames_829_);
    return v___x_830_;
}
pub unsafe fn l_Lean_Meta_Match_MatchEqns_size___boxed(
    mut v_e_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Lean_Meta_Match_MatchEqns_size(v_e_831_);
    crate::leanh::lean_dec_ref(v_e_831_);
    return v_res_832_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_833_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_833_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__0);
    v___x_835_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_835_, 0, v___x_834_);
    return v___x_835_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0(
    mut v_00_u03b2_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_837_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0___closed__1);
    return v___x_837_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_838_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0_once
        ),
        _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__0,
    );
    v___x_840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_840_, 0, v___x_839_);
    return v___x_840_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_841_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Match_instInhabitedMatchEqnsExtState_default_spec__0(crate::leanh::lean_box(0));
    return v___x_841_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_842_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__2,
    );
    v___x_843_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__1,
    );
    v___x_844_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_844_, 0, v___x_843_);
    crate::leanh::lean_ctor_set(v___x_844_, 1, v___x_842_);
    return v___x_844_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_845_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3,
    );
    return v___x_845_;
}
pub unsafe fn _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState()
-> *mut crate::leanh::LeanObject {
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
    return v___x_846_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(
    mut v___x_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_849_, 0, v___x_847_);
    return v___x_849_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed(
    mut v___x_850_: *mut crate::leanh::LeanObject,
    mut v___y_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_(v___x_850_);
    return v_res_852_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default___closed__3,
    );
    v___f_854_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_854_, 0, v___x_853_);
    return v___f_854_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_856_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_);
    v___x_857_ = crate::leanh::lean_box(0);
    v___x_858_ = crate::leanh::lean_box(1);
    v___x_859_ = l_Lean_registerEnvExtension___redArg(v___f_856_, v___x_857_, v___x_858_);
    return v___x_859_;
}
pub unsafe fn l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2____boxed(
    mut v_a_860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_();
    return v_res_861_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_x_862_: *mut crate::leanh::LeanObject,
    mut v_x_863_: *mut crate::leanh::LeanObject,
    mut v_x_864_: *mut crate::leanh::LeanObject,
    mut v_x_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: u8 = 0;
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_866_ = crate::leanh::lean_ctor_get(v_x_862_, 0);
                v_vs_867_ = crate::leanh::lean_ctor_get(v_x_862_, 1);
                v_isSharedCheck_891_ = (!crate::leanh::lean_is_exclusive(v_x_862_)) as u8;
                if v_isSharedCheck_891_ == 0 {
                    v___x_869_ = v_x_862_;
                    v_isShared_870_ = v_isSharedCheck_891_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_867_);
                    crate::leanh::lean_inc(v_ks_866_);
                    crate::leanh::lean_dec(v_x_862_);
                    v___x_869_ = crate::leanh::lean_box(0);
                    v_isShared_870_ = v_isSharedCheck_891_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_871_ = lean_array_get_size(v_ks_866_);
                v___x_872_ = lean_nat_dec_lt(v_x_863_, v___x_871_);
                if v___x_872_ == 0 {
                    crate::leanh::lean_dec(v_x_863_);
                    v___x_873_ = lean_array_push(v_ks_866_, v_x_864_);
                    v___x_874_ = lean_array_push(v_vs_867_, v_x_865_);
                    if v_isShared_870_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_869_, 1, v___x_874_);
                        crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_873_);
                        v___x_876_ = v___x_869_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_877_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_873_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_874_);
                        v___x_876_ = v_reuseFailAlloc_877_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_878_ = lean_array_fget_borrowed(v_ks_866_, v_x_863_);
                    v___x_879_ = lean_name_eq(v_x_864_, v_k_x27_878_);
                    if v___x_879_ == 0 {
                        if v_isShared_870_ == 0 {
                            v___x_881_ = v___x_869_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_885_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v_ks_866_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 1, v_vs_867_);
                            v___x_881_ = v_reuseFailAlloc_885_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_886_ = lean_array_fset(v_ks_866_, v_x_863_, v_x_864_);
                        v___x_887_ = lean_array_fset(v_vs_867_, v_x_863_, v_x_865_);
                        crate::leanh::lean_dec(v_x_863_);
                        if v_isShared_870_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_869_, 1, v___x_887_);
                            crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_886_);
                            v___x_889_ = v___x_869_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_890_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_886_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_887_);
                            v___x_889_ = v_reuseFailAlloc_890_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_876_;
            }
            3 => {
                v___x_882_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_883_ = lean_nat_add(v_x_863_, v___x_882_);
                crate::leanh::lean_dec(v_x_863_);
                v_x_862_ = v___x_881_;
                v_x_863_ = v___x_883_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(
    mut v_n_892_: *mut crate::leanh::LeanObject,
    mut v_k_893_: *mut crate::leanh::LeanObject,
    mut v_v_894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_895_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_896_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(v_n_892_, v___x_895_, v_k_893_, v_v_894_);
    return v___x_896_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u64 = 0;
    v___x_897_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_898_ = lean_uint64_of_nat(v___x_897_);
    return v___x_898_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_899_: usize = 0;
    let mut v___x_900_: usize = 0;
    let mut v___x_901_: usize = 0;
    v___x_899_ = 5usize;
    v___x_900_ = 1usize;
    v___x_901_ = lean_usize_shift_left(v___x_900_, v___x_899_);
    return v___x_901_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_902_: usize = 0;
    let mut v___x_903_: usize = 0;
    let mut v___x_904_: usize = 0;
    v___x_902_ = 1usize;
    v___x_903_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__0);
    v___x_904_ = lean_usize_sub(v___x_903_, v___x_902_);
    return v___x_904_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_905_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_905_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(
    mut v_x_906_: *mut crate::leanh::LeanObject,
    mut v_x_907_: usize,
    mut v_x_908_: usize,
    mut v_x_909_: *mut crate::leanh::LeanObject,
    mut v_x_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: usize = 0;
    let mut v___x_913_: usize = 0;
    let mut v___x_914_: usize = 0;
    let mut v___x_915_: usize = 0;
    let mut v_j_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_921_: u8 = 0;
    let mut v_v_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_935_: u8 = 0;
    let mut v___x_936_: u8 = 0;
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut v_node_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_947_: usize = 0;
    let mut v___x_948_: usize = 0;
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_953_: u8 = 0;
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_955_: u8 = 0;
    let mut v_unused_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_966_: u8 = 0;
    let mut v_ks_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: usize = 0;
    let mut v___x_973_: u8 = 0;
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: u8 = 0;
    let mut v_reuseFailAlloc_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_906_) == 0 {
                    v_es_911_ = crate::leanh::lean_ctor_get(v_x_906_, 0);
                    v___x_912_ = 5usize;
                    v___x_913_ = 1usize;
                    v___x_914_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1);
                    v___x_915_ = lean_usize_land(v_x_907_, v___x_914_);
                    v_j_916_ = lean_usize_to_nat(v___x_915_);
                    v___x_917_ = lean_array_get_size(v_es_911_);
                    v___x_918_ = lean_nat_dec_lt(v_j_916_, v___x_917_);
                    if v___x_918_ == 0 {
                        crate::leanh::lean_dec(v_j_916_);
                        crate::leanh::lean_dec(v_x_910_);
                        crate::leanh::lean_dec(v_x_909_);
                        return v_x_906_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_911_);
                        v_isSharedCheck_955_ = (!crate::leanh::lean_is_exclusive(v_x_906_)) as u8;
                        if v_isSharedCheck_955_ == 0 {
                            v_unused_956_ = crate::leanh::lean_ctor_get(v_x_906_, 0);
                            crate::leanh::lean_dec(v_unused_956_);
                            v___x_920_ = v_x_906_;
                            v_isShared_921_ = v_isSharedCheck_955_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_906_);
                            v___x_920_ = crate::leanh::lean_box(0);
                            v_isShared_921_ = v_isSharedCheck_955_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_957_ = crate::leanh::lean_ctor_get(v_x_906_, 0);
                    v_vs_958_ = crate::leanh::lean_ctor_get(v_x_906_, 1);
                    v_isSharedCheck_978_ = (!crate::leanh::lean_is_exclusive(v_x_906_)) as u8;
                    if v_isSharedCheck_978_ == 0 {
                        v___x_960_ = v_x_906_;
                        v_isShared_961_ = v_isSharedCheck_978_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_958_);
                        crate::leanh::lean_inc(v_ks_957_);
                        crate::leanh::lean_dec(v_x_906_);
                        v___x_960_ = crate::leanh::lean_box(0);
                        v_isShared_961_ = v_isSharedCheck_978_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_922_ = lean_array_fget(v_es_911_, v_j_916_);
                v___x_923_ = crate::leanh::lean_box(0);
                v_xs_x27_924_ = lean_array_fset(v_es_911_, v_j_916_, v___x_923_);
                match crate::leanh::lean_obj_tag(v_v_922_) {
                    0 => {
                        v_key_931_ = crate::leanh::lean_ctor_get(v_v_922_, 0);
                        v_val_932_ = crate::leanh::lean_ctor_get(v_v_922_, 1);
                        v_isSharedCheck_942_ = (!crate::leanh::lean_is_exclusive(v_v_922_)) as u8;
                        if v_isSharedCheck_942_ == 0 {
                            v___x_934_ = v_v_922_;
                            v_isShared_935_ = v_isSharedCheck_942_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_932_);
                            crate::leanh::lean_inc(v_key_931_);
                            crate::leanh::lean_dec(v_v_922_);
                            v___x_934_ = crate::leanh::lean_box(0);
                            v_isShared_935_ = v_isSharedCheck_942_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_943_ = crate::leanh::lean_ctor_get(v_v_922_, 0);
                        v_isSharedCheck_953_ = (!crate::leanh::lean_is_exclusive(v_v_922_)) as u8;
                        if v_isSharedCheck_953_ == 0 {
                            v___x_945_ = v_v_922_;
                            v_isShared_946_ = v_isSharedCheck_953_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_943_);
                            crate::leanh::lean_dec(v_v_922_);
                            v___x_945_ = crate::leanh::lean_box(0);
                            v_isShared_946_ = v_isSharedCheck_953_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_954_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_954_, 0, v_x_909_);
                        crate::leanh::lean_ctor_set(v___x_954_, 1, v_x_910_);
                        v___y_926_ = v___x_954_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_927_ = lean_array_fset(v_xs_x27_924_, v_j_916_, v___y_926_);
                crate::leanh::lean_dec(v_j_916_);
                if v_isShared_921_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_920_, 0, v___x_927_);
                    v___x_929_ = v___x_920_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
                    v___x_929_ = v_reuseFailAlloc_930_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_929_;
            }
            4 => {
                v___x_936_ = lean_name_eq(v_x_909_, v_key_931_);
                if v___x_936_ == 0 {
                    crate::leanh::lean_del_object(v___x_934_);
                    v___x_937_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_931_, v_val_932_, v_x_909_, v_x_910_,
                    );
                    v___x_938_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_938_, 0, v___x_937_);
                    v___y_926_ = v___x_938_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_932_);
                    crate::leanh::lean_dec(v_key_931_);
                    if v_isShared_935_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_934_, 1, v_x_910_);
                        crate::leanh::lean_ctor_set(v___x_934_, 0, v_x_909_);
                        v___x_940_ = v___x_934_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_941_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 0, v_x_909_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 1, v_x_910_);
                        v___x_940_ = v_reuseFailAlloc_941_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_926_ = v___x_940_;
                state = 2;
                continue;
            }
            6 => {
                v___x_947_ = lean_usize_shift_right(v_x_907_, v___x_912_);
                v___x_948_ = lean_usize_add(v_x_908_, v___x_913_);
                v___x_949_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_node_943_, v___x_947_, v___x_948_, v_x_909_, v_x_910_);
                if v_isShared_946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_945_, 0, v___x_949_);
                    v___x_951_ = v___x_945_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_952_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
                    v___x_951_ = v_reuseFailAlloc_952_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_926_ = v___x_951_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_961_ == 0 {
                    v___x_963_ = v___x_960_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_977_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 0, v_ks_957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_977_, 1, v_vs_958_);
                    v___x_963_ = v_reuseFailAlloc_977_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_964_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(v___x_963_, v_x_909_, v_x_910_);
                v___x_972_ = 7usize;
                v___x_973_ = lean_usize_dec_le(v___x_972_, v_x_908_);
                if v___x_973_ == 0 {
                    v___x_974_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_964_);
                    v___x_975_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_976_ = lean_nat_dec_lt(v___x_974_, v___x_975_);
                    crate::leanh::lean_dec(v___x_974_);
                    v___y_966_ = v___x_976_;
                    state = 10;
                    continue;
                } else {
                    v___y_966_ = v___x_973_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_966_ == 0 {
                    v_ks_967_ = crate::leanh::lean_ctor_get(v_newNode_964_, 0);
                    crate::leanh::lean_inc_ref(v_ks_967_);
                    v_vs_968_ = crate::leanh::lean_ctor_get(v_newNode_964_, 1);
                    crate::leanh::lean_inc_ref(v_vs_968_);
                    crate::leanh::lean_dec_ref(v_newNode_964_);
                    v___x_969_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_970_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__2);
                    v___x_971_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_x_908_, v_ks_967_, v_vs_968_, v___x_969_, v___x_970_);
                    crate::leanh::lean_dec_ref(v_vs_968_);
                    crate::leanh::lean_dec_ref(v_ks_967_);
                    return v___x_971_;
                } else {
                    return v_newNode_964_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(
    mut v_depth_979_: usize,
    mut v_keys_980_: *mut crate::leanh::LeanObject,
    mut v_vals_981_: *mut crate::leanh::LeanObject,
    mut v_i_982_: *mut crate::leanh::LeanObject,
    mut v_entries_983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: u8 = 0;
    let mut v_k_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_989_: u64 = 0;
    let mut v_h_990_: usize = 0;
    let mut v___x_991_: usize = 0;
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: usize = 0;
    let mut v___x_994_: usize = 0;
    let mut v___x_995_: usize = 0;
    let mut v_h_996_: usize = 0;
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u64 = 0;
    let mut v_hash_1001_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_984_ = lean_array_get_size(v_keys_980_);
                v___x_985_ = lean_nat_dec_lt(v_i_982_, v___x_984_);
                if v___x_985_ == 0 {
                    crate::leanh::lean_dec(v_i_982_);
                    return v_entries_983_;
                } else {
                    v_k_986_ = lean_array_fget_borrowed(v_keys_980_, v_i_982_);
                    v_v_987_ = lean_array_fget_borrowed(v_vals_981_, v_i_982_);
                    if crate::leanh::lean_obj_tag(v_k_986_) == 0 {
                        v___x_1000_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_989_ = v___x_1000_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_1001_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_986_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_989_ = v_hash_1001_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_990_ = lean_uint64_to_usize(v___y_989_);
                v___x_991_ = 5usize;
                v___x_992_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_993_ = 1usize;
                v___x_994_ = lean_usize_sub(v_depth_979_, v___x_993_);
                v___x_995_ = lean_usize_mul(v___x_991_, v___x_994_);
                v_h_996_ = lean_usize_shift_right(v_h_990_, v___x_995_);
                v___x_997_ = lean_nat_add(v_i_982_, v___x_992_);
                crate::leanh::lean_dec(v_i_982_);
                crate::leanh::lean_inc(v_v_987_);
                crate::leanh::lean_inc(v_k_986_);
                v___x_998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_entries_983_, v_h_996_, v_depth_979_, v_k_986_, v_v_987_);
                v_i_982_ = v___x_997_;
                v_entries_983_ = v___x_998_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_1002_: *mut crate::leanh::LeanObject,
    mut v_keys_1003_: *mut crate::leanh::LeanObject,
    mut v_vals_1004_: *mut crate::leanh::LeanObject,
    mut v_i_1005_: *mut crate::leanh::LeanObject,
    mut v_entries_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1007_: usize = 0;
    let mut v_res_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1007_ = crate::leanh::lean_unbox_usize(v_depth_1002_);
    crate::leanh::lean_dec(v_depth_1002_);
    v_res_1008_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1007_, v_keys_1003_, v_vals_1004_, v_i_1005_, v_entries_1006_);
    crate::leanh::lean_dec_ref(v_vals_1004_);
    crate::leanh::lean_dec_ref(v_keys_1003_);
    return v_res_1008_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___boxed(
    mut v_x_1009_: *mut crate::leanh::LeanObject,
    mut v_x_1010_: *mut crate::leanh::LeanObject,
    mut v_x_1011_: *mut crate::leanh::LeanObject,
    mut v_x_1012_: *mut crate::leanh::LeanObject,
    mut v_x_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_719__boxed_1014_: usize = 0;
    let mut v_x_720__boxed_1015_: usize = 0;
    let mut v_res_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_719__boxed_1014_ = crate::leanh::lean_unbox_usize(v_x_1010_);
    crate::leanh::lean_dec(v_x_1010_);
    v_x_720__boxed_1015_ = crate::leanh::lean_unbox_usize(v_x_1011_);
    crate::leanh::lean_dec(v_x_1011_);
    v_res_1016_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_1009_, v_x_719__boxed_1014_, v_x_720__boxed_1015_, v_x_1012_, v_x_1013_);
    return v_res_1016_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(
    mut v_x_1017_: *mut crate::leanh::LeanObject,
    mut v_x_1018_: *mut crate::leanh::LeanObject,
    mut v_x_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1021_: u64 = 0;
    let mut v___x_1022_: usize = 0;
    let mut v___x_1023_: usize = 0;
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: u64 = 0;
    let mut v_hash_1026_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1018_) == 0 {
                    v___x_1025_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_1021_ = v___x_1025_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1026_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_1018_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1021_ = v_hash_1026_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1022_ = lean_uint64_to_usize(v___y_1021_);
                v___x_1023_ = 1usize;
                v___x_1024_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_1017_, v___x_1022_, v___x_1023_, v_x_1018_, v_x_1019_);
                return v___x_1024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(
    mut v_as_1027_: *mut crate::leanh::LeanObject,
    mut v_i_1028_: usize,
    mut v_stop_1029_: usize,
    mut v_b_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1031_: u8 = 0;
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: usize = 0;
    let mut v___x_1036_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1031_ = lean_usize_dec_eq(v_i_1028_, v_stop_1029_);
                if v___x_1031_ == 0 {
                    v___x_1032_ = lean_array_uget_borrowed(v_as_1027_, v_i_1028_);
                    v___x_1033_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___x_1032_);
                    v___x_1034_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_b_1030_, v___x_1032_, v___x_1033_);
                    v___x_1035_ = 1usize;
                    v___x_1036_ = lean_usize_add(v_i_1028_, v___x_1035_);
                    v_i_1028_ = v___x_1036_;
                    v_b_1030_ = v___x_1034_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1030_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1___boxed(
    mut v_as_1038_: *mut crate::leanh::LeanObject,
    mut v_i_1039_: *mut crate::leanh::LeanObject,
    mut v_stop_1040_: *mut crate::leanh::LeanObject,
    mut v_b_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1042_: usize = 0;
    let mut v_stop_boxed_1043_: usize = 0;
    let mut v_res_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1042_ = crate::leanh::lean_unbox_usize(v_i_1039_);
    crate::leanh::lean_dec(v_i_1039_);
    v_stop_boxed_1043_ = crate::leanh::lean_unbox_usize(v_stop_1040_);
    crate::leanh::lean_dec(v_stop_1040_);
    v_res_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_as_1038_, v_i_boxed_1042_, v_stop_boxed_1043_, v_b_1041_);
    crate::leanh::lean_dec_ref(v_as_1038_);
    return v_res_1044_;
}
pub unsafe fn l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0(
    mut v_matchEqns_1045_: *mut crate::leanh::LeanObject,
    mut v_matchDeclName_1046_: *mut crate::leanh::LeanObject,
    mut v_x_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqns_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v_eqnNames_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: u8 = 0;
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: u8 = 0;
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: usize = 0;
    let mut v___x_1066_: usize = 0;
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: usize = 0;
    let mut v___x_1072_: usize = 0;
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1048_ = crate::leanh::lean_ctor_get(v_x_1047_, 0);
                v_eqns_1049_ = crate::leanh::lean_ctor_get(v_x_1047_, 1);
                v_isSharedCheck_1077_ = (!crate::leanh::lean_is_exclusive(v_x_1047_)) as u8;
                if v_isSharedCheck_1077_ == 0 {
                    v___x_1051_ = v_x_1047_;
                    v_isShared_1052_ = v_isSharedCheck_1077_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_eqns_1049_);
                    crate::leanh::lean_inc(v_map_1048_);
                    crate::leanh::lean_dec(v_x_1047_);
                    v___x_1051_ = crate::leanh::lean_box(0);
                    v_isShared_1052_ = v_isSharedCheck_1077_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_eqnNames_1053_ = crate::leanh::lean_ctor_get(v_matchEqns_1045_, 0);
                crate::leanh::lean_inc_ref(v_eqnNames_1053_);
                v___x_1054_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(v_map_1048_, v_matchDeclName_1046_, v_matchEqns_1045_);
                v___x_1055_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1056_ = lean_array_get_size(v_eqnNames_1053_);
                v___x_1057_ = lean_nat_dec_lt(v___x_1055_, v___x_1056_);
                if v___x_1057_ == 0 {
                    crate::leanh::lean_dec_ref(v_eqnNames_1053_);
                    if v_isShared_1052_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1051_, 0, v___x_1054_);
                        v___x_1059_ = v___x_1051_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1060_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1054_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_eqns_1049_);
                        v___x_1059_ = v_reuseFailAlloc_1060_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1061_ = lean_nat_dec_le(v___x_1056_, v___x_1056_);
                    if v___x_1061_ == 0 {
                        if v___x_1057_ == 0 {
                            crate::leanh::lean_dec_ref(v_eqnNames_1053_);
                            if v_isShared_1052_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1051_, 0, v___x_1054_);
                                v___x_1063_ = v___x_1051_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1064_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1054_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1064_,
                                    1,
                                    v_eqns_1049_,
                                );
                                v___x_1063_ = v_reuseFailAlloc_1064_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_1065_ = 0usize;
                            v___x_1066_ = lean_usize_of_nat(v___x_1056_);
                            v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_1053_, v___x_1065_, v___x_1066_, v_eqns_1049_);
                            crate::leanh::lean_dec_ref(v_eqnNames_1053_);
                            if v_isShared_1052_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1051_, 1, v___x_1067_);
                                crate::leanh::lean_ctor_set(v___x_1051_, 0, v___x_1054_);
                                v___x_1069_ = v___x_1051_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1070_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1054_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1067_);
                                v___x_1069_ = v_reuseFailAlloc_1070_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_1071_ = 0usize;
                        v___x_1072_ = lean_usize_of_nat(v___x_1056_);
                        v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_registerMatchEqns_spec__1(v_eqnNames_1053_, v___x_1071_, v___x_1072_, v_eqns_1049_);
                        crate::leanh::lean_dec_ref(v_eqnNames_1053_);
                        if v_isShared_1052_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1051_, 1, v___x_1073_);
                            crate::leanh::lean_ctor_set(v___x_1051_, 0, v___x_1054_);
                            v___x_1075_ = v___x_1051_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1076_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1054_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___x_1073_);
                            v___x_1075_ = v_reuseFailAlloc_1076_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1059_;
            }
            3 => {
                return v___x_1063_;
            }
            4 => {
                return v___x_1069_;
            }
            5 => {
                return v___x_1075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1078_;
}
pub unsafe fn _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1079_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0_once),
        _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__0,
    );
    v___x_1080_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1079_);
    return v___x_1080_;
}
pub unsafe fn _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1_once),
        _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__1,
    );
    v___x_1082_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1082_, 0, v___x_1081_);
    crate::leanh::lean_ctor_set(v___x_1082_, 1, v___x_1081_);
    return v___x_1082_;
}
pub unsafe fn l_Lean_Meta_Match_registerMatchEqns___redArg(
    mut v_matchDeclName_1083_: *mut crate::leanh::LeanObject,
    mut v_matchEqns_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v_unused_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1087_ = lean_st_ref_take(v_a_1085_);
                v_env_1088_ = crate::leanh::lean_ctor_get(v___x_1087_, 0);
                v_nextMacroScope_1089_ = crate::leanh::lean_ctor_get(v___x_1087_, 1);
                v_ngen_1090_ = crate::leanh::lean_ctor_get(v___x_1087_, 2);
                v_auxDeclNGen_1091_ = crate::leanh::lean_ctor_get(v___x_1087_, 3);
                v_traceState_1092_ = crate::leanh::lean_ctor_get(v___x_1087_, 4);
                v_messages_1093_ = crate::leanh::lean_ctor_get(v___x_1087_, 6);
                v_infoState_1094_ = crate::leanh::lean_ctor_get(v___x_1087_, 7);
                v_snapshotTasks_1095_ = crate::leanh::lean_ctor_get(v___x_1087_, 8);
                v_isSharedCheck_1111_ = (!crate::leanh::lean_is_exclusive(v___x_1087_)) as u8;
                if v_isSharedCheck_1111_ == 0 {
                    v_unused_1112_ = crate::leanh::lean_ctor_get(v___x_1087_, 5);
                    crate::leanh::lean_dec(v_unused_1112_);
                    v___x_1097_ = v___x_1087_;
                    v_isShared_1098_ = v_isSharedCheck_1111_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1095_);
                    crate::leanh::lean_inc(v_infoState_1094_);
                    crate::leanh::lean_inc(v_messages_1093_);
                    crate::leanh::lean_inc(v_traceState_1092_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1091_);
                    crate::leanh::lean_inc(v_ngen_1090_);
                    crate::leanh::lean_inc(v_nextMacroScope_1089_);
                    crate::leanh::lean_inc(v_env_1088_);
                    crate::leanh::lean_dec(v___x_1087_);
                    v___x_1097_ = crate::leanh::lean_box(0);
                    v_isShared_1098_ = v_isSharedCheck_1111_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1099_ = l_Lean_Meta_Match_matchEqnsExt;
                v_asyncMode_1100_ = crate::leanh::lean_ctor_get(v___x_1099_, 2);
                v___f_1101_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Match_registerMatchEqns___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1101_, 0, v_matchEqns_1084_);
                crate::leanh::lean_closure_set(v___f_1101_, 1, v_matchDeclName_1083_);
                v___x_1102_ = crate::leanh::lean_box(0);
                v___x_1103_ = l_Lean_EnvExtension_modifyState___redArg(
                    v___x_1099_,
                    v_env_1088_,
                    v___f_1101_,
                    v_asyncMode_1100_,
                    v___x_1102_,
                );
                v___x_1104_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Match_registerMatchEqns___redArg___closed__2,
                );
                if v_isShared_1098_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1097_, 5, v___x_1104_);
                    crate::leanh::lean_ctor_set(v___x_1097_, 0, v___x_1103_);
                    v___x_1106_ = v___x_1097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_nextMacroScope_1089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_ngen_1090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_auxDeclNGen_1091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 4, v_traceState_1092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 5, v___x_1104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 6, v_messages_1093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 7, v_infoState_1094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 8, v_snapshotTasks_1095_);
                    v___x_1106_ = v_reuseFailAlloc_1110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1107_ = lean_st_ref_set(v_a_1085_, v___x_1106_);
                v___x_1108_ = crate::leanh::lean_box(0);
                v___x_1109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1109_, 0, v___x_1108_);
                return v___x_1109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_registerMatchEqns___redArg___boxed(
    mut v_matchDeclName_1113_: *mut crate::leanh::LeanObject,
    mut v_matchEqns_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_Lean_Meta_Match_registerMatchEqns___redArg(
        v_matchDeclName_1113_,
        v_matchEqns_1114_,
        v_a_1115_,
    );
    crate::leanh::lean_dec(v_a_1115_);
    return v_res_1117_;
}
pub unsafe fn l_Lean_Meta_Match_registerMatchEqns(
    mut v_matchDeclName_1118_: *mut crate::leanh::LeanObject,
    mut v_matchEqns_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_Meta_Match_registerMatchEqns___redArg(
        v_matchDeclName_1118_,
        v_matchEqns_1119_,
        v_a_1121_,
    );
    return v___x_1123_;
}
pub unsafe fn l_Lean_Meta_Match_registerMatchEqns___boxed(
    mut v_matchDeclName_1124_: *mut crate::leanh::LeanObject,
    mut v_matchEqns_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1129_ = l_Lean_Meta_Match_registerMatchEqns(
        v_matchDeclName_1124_,
        v_matchEqns_1125_,
        v_a_1126_,
        v_a_1127_,
    );
    crate::leanh::lean_dec(v_a_1127_);
    crate::leanh::lean_dec_ref(v_a_1126_);
    return v_res_1129_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0(
    mut v_00_u03b2_1130_: *mut crate::leanh::LeanObject,
    mut v_x_1131_: *mut crate::leanh::LeanObject,
    mut v_x_1132_: *mut crate::leanh::LeanObject,
    mut v_x_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1134_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0___redArg(
            v_x_1131_, v_x_1132_, v_x_1133_,
        );
    return v___x_1134_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(
    mut v_00_u03b2_1135_: *mut crate::leanh::LeanObject,
    mut v_x_1136_: *mut crate::leanh::LeanObject,
    mut v_x_1137_: usize,
    mut v_x_1138_: usize,
    mut v_x_1139_: *mut crate::leanh::LeanObject,
    mut v_x_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1141_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg(v_x_1136_, v_x_1137_, v_x_1138_, v_x_1139_, v_x_1140_);
    return v___x_1141_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___boxed(
    mut v_00_u03b2_1142_: *mut crate::leanh::LeanObject,
    mut v_x_1143_: *mut crate::leanh::LeanObject,
    mut v_x_1144_: *mut crate::leanh::LeanObject,
    mut v_x_1145_: *mut crate::leanh::LeanObject,
    mut v_x_1146_: *mut crate::leanh::LeanObject,
    mut v_x_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1047__boxed_1148_: usize = 0;
    let mut v_x_1048__boxed_1149_: usize = 0;
    let mut v_res_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1047__boxed_1148_ = crate::leanh::lean_unbox_usize(v_x_1144_);
    crate::leanh::lean_dec(v_x_1144_);
    v_x_1048__boxed_1149_ = crate::leanh::lean_unbox_usize(v_x_1145_);
    crate::leanh::lean_dec(v_x_1145_);
    v_res_1150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0(v_00_u03b2_1142_, v_x_1143_, v_x_1047__boxed_1148_, v_x_1048__boxed_1149_, v_x_1146_, v_x_1147_);
    return v_res_1150_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1151_: *mut crate::leanh::LeanObject,
    mut v_n_1152_: *mut crate::leanh::LeanObject,
    mut v_k_1153_: *mut crate::leanh::LeanObject,
    mut v_v_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1___redArg(v_n_1152_, v_k_1153_, v_v_1154_);
    return v___x_1155_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1156_: *mut crate::leanh::LeanObject,
    mut v_depth_1157_: usize,
    mut v_keys_1158_: *mut crate::leanh::LeanObject,
    mut v_vals_1159_: *mut crate::leanh::LeanObject,
    mut v_heq_1160_: *mut crate::leanh::LeanObject,
    mut v_i_1161_: *mut crate::leanh::LeanObject,
    mut v_entries_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1163_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg(v_depth_1157_, v_keys_1158_, v_vals_1159_, v_i_1161_, v_entries_1162_);
    return v___x_1163_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1164_: *mut crate::leanh::LeanObject,
    mut v_depth_1165_: *mut crate::leanh::LeanObject,
    mut v_keys_1166_: *mut crate::leanh::LeanObject,
    mut v_vals_1167_: *mut crate::leanh::LeanObject,
    mut v_heq_1168_: *mut crate::leanh::LeanObject,
    mut v_i_1169_: *mut crate::leanh::LeanObject,
    mut v_entries_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1171_: usize = 0;
    let mut v_res_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1171_ = crate::leanh::lean_unbox_usize(v_depth_1165_);
    crate::leanh::lean_dec(v_depth_1165_);
    v_res_1172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2(v_00_u03b2_1164_, v_depth_boxed_1171_, v_keys_1166_, v_vals_1167_, v_heq_1168_, v_i_1169_, v_entries_1170_);
    crate::leanh::lean_dec_ref(v_vals_1167_);
    crate::leanh::lean_dec_ref(v_keys_1166_);
    return v_res_1172_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_1173_: *mut crate::leanh::LeanObject,
    mut v_x_1174_: *mut crate::leanh::LeanObject,
    mut v_x_1175_: *mut crate::leanh::LeanObject,
    mut v_x_1176_: *mut crate::leanh::LeanObject,
    mut v_x_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1178_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1174_, v_x_1175_, v_x_1176_, v_x_1177_);
    return v___x_1178_;
}
pub unsafe fn l_Lean_Meta_Match_getEquationsFor___boxed(
    mut v_matchDeclName_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1191_ = lean_get_match_equations_for(
        v_matchDeclName_1185_,
        v_a_1186_,
        v_a_1187_,
        v_a_1188_,
        v_a_1189_,
    );
    return v_res_1191_;
}
pub unsafe fn l_Lean_Meta_Match_genMatchCongrEqns___boxed(
    mut v_matchDeclName_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
    mut v_a_1201_: *mut crate::leanh::LeanObject,
    mut v_a_1202_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1204_ = lean_get_congr_match_equations_for(
        v_matchDeclName_1198_,
        v_a_1199_,
        v_a_1200_,
        v_a_1201_,
        v_a_1202_,
    );
    return v_res_1204_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1205_: *mut crate::leanh::LeanObject,
    mut v_i_1206_: *mut crate::leanh::LeanObject,
    mut v_k_1207_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: u8 = 0;
    let mut v_k_x27_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: u8 = 0;
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1208_ = lean_array_get_size(v_keys_1205_);
                v___x_1209_ = lean_nat_dec_lt(v_i_1206_, v___x_1208_);
                if v___x_1209_ == 0 {
                    crate::leanh::lean_dec(v_i_1206_);
                    return v___x_1209_;
                } else {
                    v_k_x27_1210_ = lean_array_fget_borrowed(v_keys_1205_, v_i_1206_);
                    v___x_1211_ = lean_name_eq(v_k_1207_, v_k_x27_1210_);
                    if v___x_1211_ == 0 {
                        v___x_1212_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1213_ = lean_nat_add(v_i_1206_, v___x_1212_);
                        crate::leanh::lean_dec(v_i_1206_);
                        v_i_1206_ = v___x_1213_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_1206_);
                        return v___x_1211_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1215_: *mut crate::leanh::LeanObject,
    mut v_i_1216_: *mut crate::leanh::LeanObject,
    mut v_k_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1218_: u8 = 0;
    let mut v_r_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1218_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1215_, v_i_1216_, v_k_1217_);
    crate::leanh::lean_dec(v_k_1217_);
    crate::leanh::lean_dec_ref(v_keys_1215_);
    v_r_1219_ = crate::leanh::lean_box((v_res_1218_) as usize);
    return v_r_1219_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(
    mut v_x_1220_: *mut crate::leanh::LeanObject,
    mut v_x_1221_: usize,
    mut v_x_1222_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: usize = 0;
    let mut v___x_1226_: usize = 0;
    let mut v___x_1227_: usize = 0;
    let mut v_j_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: u8 = 0;
    let mut v_node_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: usize = 0;
    let mut v___x_1235_: u8 = 0;
    let mut v_ks_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1220_) == 0 {
                    v_es_1223_ = crate::leanh::lean_ctor_get(v_x_1220_, 0);
                    v___x_1224_ = crate::leanh::lean_box(2);
                    v___x_1225_ = 5usize;
                    v___x_1226_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0___redArg___closed__1);
                    v___x_1227_ = lean_usize_land(v_x_1221_, v___x_1226_);
                    v_j_1228_ = lean_usize_to_nat(v___x_1227_);
                    v___x_1229_ = lean_array_get_borrowed(v___x_1224_, v_es_1223_, v_j_1228_);
                    crate::leanh::lean_dec(v_j_1228_);
                    match crate::leanh::lean_obj_tag(v___x_1229_) {
                        0 => {
                            v_key_1230_ = crate::leanh::lean_ctor_get(v___x_1229_, 0);
                            v___x_1231_ = lean_name_eq(v_x_1222_, v_key_1230_);
                            return v___x_1231_;
                        }
                        1 => {
                            v_node_1232_ = crate::leanh::lean_ctor_get(v___x_1229_, 0);
                            v___x_1233_ = lean_usize_shift_right(v_x_1221_, v___x_1225_);
                            v_x_1220_ = v_node_1232_;
                            v_x_1221_ = v___x_1233_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1235_ = 0;
                            return v___x_1235_;
                        }
                    }
                } else {
                    v_ks_1236_ = crate::leanh::lean_ctor_get(v_x_1220_, 0);
                    v___x_1237_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1238_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_ks_1236_, v___x_1237_, v_x_1222_);
                    return v___x_1238_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg___boxed(
    mut v_x_1239_: *mut crate::leanh::LeanObject,
    mut v_x_1240_: *mut crate::leanh::LeanObject,
    mut v_x_1241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_344__boxed_1242_: usize = 0;
    let mut v_res_1243_: u8 = 0;
    let mut v_r_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_344__boxed_1242_ = crate::leanh::lean_unbox_usize(v_x_1240_);
    crate::leanh::lean_dec(v_x_1240_);
    v_res_1243_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_1239_, v_x_344__boxed_1242_, v_x_1241_);
    crate::leanh::lean_dec(v_x_1241_);
    crate::leanh::lean_dec_ref(v_x_1239_);
    v_r_1244_ = crate::leanh::lean_box((v_res_1243_) as usize);
    return v_r_1244_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(
    mut v_x_1245_: *mut crate::leanh::LeanObject,
    mut v_x_1246_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_1248_: u64 = 0;
    let mut v___x_1249_: usize = 0;
    let mut v___x_1250_: u8 = 0;
    let mut v___x_1251_: u64 = 0;
    let mut v_hash_1252_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1246_) == 0 {
                    v___x_1251_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Match_registerMatchEqns_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_1248_ = v___x_1251_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1252_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_1246_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1248_ = v_hash_1252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1249_ = lean_uint64_to_usize(v___y_1248_);
                v___x_1250_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_1245_, v___x_1249_, v_x_1246_);
                return v___x_1250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg___boxed(
    mut v_x_1253_: *mut crate::leanh::LeanObject,
    mut v_x_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1255_: u8 = 0;
    let mut v_r_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_1253_, v_x_1254_);
    crate::leanh::lean_dec(v_x_1254_);
    crate::leanh::lean_dec_ref(v_x_1253_);
    v_r_1256_ = crate::leanh::lean_box((v_res_1255_) as usize);
    return v_r_1256_;
}
pub unsafe fn l_Lean_Meta_Match_isMatchEqnTheorem(
    mut v_env_1259_: *mut crate::leanh::LeanObject,
    mut v_declName_1260_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_declName_1260_);
    v___x_1261_ = lean_erase_macro_scopes(v_declName_1260_);
    if crate::leanh::lean_obj_tag(v___x_1261_) == 1 {
        let mut v_str_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: u8 = 0;
        v_str_1262_ = crate::leanh::lean_ctor_get(v___x_1261_, 1);
        crate::leanh::lean_inc_ref(v_str_1262_);
        crate::leanh::lean_dec_ref_known(v___x_1261_, 2);
        v___x_1263_ = l_Lean_Meta_isEqnLikeSuffix(v_str_1262_);
        if v___x_1263_ == 0 {
            crate::leanh::lean_dec(v_declName_1260_);
            crate::leanh::lean_dec_ref(v_env_1259_);
            return v___x_1263_;
        } else {
            let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_eqns_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1269_: u8 = 0;
            v___x_1264_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
            v___x_1265_ = l_Lean_Meta_Match_matchEqnsExt;
            v___x_1266_ = l_Lean_Meta_Match_isMatchEqnTheorem___closed__0;
            crate::leanh::lean_inc(v_declName_1260_);
            v___x_1267_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                v___x_1264_,
                v___x_1265_,
                v_env_1259_,
                v___x_1266_,
                v_declName_1260_,
            );
            v_eqns_1268_ = crate::leanh::lean_ctor_get(v___x_1267_, 1);
            crate::leanh::lean_inc_ref(v_eqns_1268_);
            crate::leanh::lean_dec(v___x_1267_);
            v___x_1269_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_eqns_1268_, v_declName_1260_);
            crate::leanh::lean_dec(v_declName_1260_);
            crate::leanh::lean_dec_ref(v_eqns_1268_);
            return v___x_1269_;
        }
    } else {
        let mut v___x_1270_: u8 = 0;
        crate::leanh::lean_dec(v___x_1261_);
        crate::leanh::lean_dec(v_declName_1260_);
        crate::leanh::lean_dec_ref(v_env_1259_);
        v___x_1270_ = 0;
        return v___x_1270_;
    }
}
pub unsafe fn l_Lean_Meta_Match_isMatchEqnTheorem___boxed(
    mut v_env_1271_: *mut crate::leanh::LeanObject,
    mut v_declName_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1273_: u8 = 0;
    let mut v_r_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1273_ = l_Lean_Meta_Match_isMatchEqnTheorem(v_env_1271_, v_declName_1272_);
    v_r_1274_ = crate::leanh::lean_box((v_res_1273_) as usize);
    return v_r_1274_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(
    mut v_00_u03b2_1275_: *mut crate::leanh::LeanObject,
    mut v_x_1276_: *mut crate::leanh::LeanObject,
    mut v_x_1277_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1278_: u8 = 0;
    v___x_1278_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___redArg(v_x_1276_, v_x_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0___boxed(
    mut v_00_u03b2_1279_: *mut crate::leanh::LeanObject,
    mut v_x_1280_: *mut crate::leanh::LeanObject,
    mut v_x_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1282_: u8 = 0;
    let mut v_r_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1282_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0(
            v_00_u03b2_1279_,
            v_x_1280_,
            v_x_1281_,
        );
    crate::leanh::lean_dec(v_x_1281_);
    crate::leanh::lean_dec_ref(v_x_1280_);
    v_r_1283_ = crate::leanh::lean_box((v_res_1282_) as usize);
    return v_r_1283_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(
    mut v_00_u03b2_1284_: *mut crate::leanh::LeanObject,
    mut v_x_1285_: *mut crate::leanh::LeanObject,
    mut v_x_1286_: usize,
    mut v_x_1287_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1288_: u8 = 0;
    v___x_1288_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___redArg(v_x_1285_, v_x_1286_, v_x_1287_);
    return v___x_1288_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0___boxed(
    mut v_00_u03b2_1289_: *mut crate::leanh::LeanObject,
    mut v_x_1290_: *mut crate::leanh::LeanObject,
    mut v_x_1291_: *mut crate::leanh::LeanObject,
    mut v_x_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_439__boxed_1293_: usize = 0;
    let mut v_res_1294_: u8 = 0;
    let mut v_r_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_439__boxed_1293_ = crate::leanh::lean_unbox_usize(v_x_1291_);
    crate::leanh::lean_dec(v_x_1291_);
    v_res_1294_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0(v_00_u03b2_1289_, v_x_1290_, v_x_439__boxed_1293_, v_x_1292_);
    crate::leanh::lean_dec(v_x_1292_);
    crate::leanh::lean_dec_ref(v_x_1290_);
    v_r_1295_ = crate::leanh::lean_box((v_res_1294_) as usize);
    return v_r_1295_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1296_: *mut crate::leanh::LeanObject,
    mut v_keys_1297_: *mut crate::leanh::LeanObject,
    mut v_vals_1298_: *mut crate::leanh::LeanObject,
    mut v_heq_1299_: *mut crate::leanh::LeanObject,
    mut v_i_1300_: *mut crate::leanh::LeanObject,
    mut v_k_1301_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1302_: u8 = 0;
    v___x_1302_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1297_, v_i_1300_, v_k_1301_);
    return v___x_1302_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1303_: *mut crate::leanh::LeanObject,
    mut v_keys_1304_: *mut crate::leanh::LeanObject,
    mut v_vals_1305_: *mut crate::leanh::LeanObject,
    mut v_heq_1306_: *mut crate::leanh::LeanObject,
    mut v_i_1307_: *mut crate::leanh::LeanObject,
    mut v_k_1308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1309_: u8 = 0;
    let mut v_r_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1309_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Match_isMatchEqnTheorem_spec__0_spec__0_spec__1(v_00_u03b2_1303_, v_keys_1304_, v_vals_1305_, v_heq_1306_, v_i_1307_, v_k_1308_);
    crate::leanh::lean_dec(v_k_1308_);
    crate::leanh::lean_dec_ref(v_vals_1305_);
    crate::leanh::lean_dec_ref(v_keys_1304_);
    v_r_1310_ = crate::leanh::lean_box((v_res_1309_) as usize);
    return v_r_1310_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_MatchEqsExt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Match_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Match_instInhabitedMatchEqns_default =
        _init_l_Lean_Meta_Match_instInhabitedMatchEqns_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatchEqns_default);
    l_Lean_Meta_Match_instInhabitedMatchEqns = _init_l_Lean_Meta_Match_instInhabitedMatchEqns();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatchEqns);
    l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default =
        _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default);
    l_Lean_Meta_Match_instInhabitedMatchEqnsExtState =
        _init_l_Lean_Meta_Match_instInhabitedMatchEqnsExtState();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatchEqnsExtState);
    res = l___private_Lean_Meta_Match_MatchEqsExt_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqsExt_1276161115____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Match_matchEqnsExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Match_matchEqnsExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_MatchEqsExt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_MatchEqsExt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Match_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatchEqsExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_MatchEqsExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_MatchEqsExt(builtin);
}

// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.RecArgInfo
// Imports: Lean.Elab.PreDefinition.FixedParams Lean.Elab.PreDefinition.Structural.IndGroupInfo
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::{
    initialize_Lean_Elab_PreDefinition_FixedParams, l_Lean_Elab_FixedParamPerm_buildArgs___redArg,
    l_Lean_Elab_FixedParamPerm_isFixed, l_Lean_Elab_FixedParamPerm_numFixed,
    runtime_initialize_Lean_Elab_PreDefinition_FixedParams,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::IndGroupInfo::{
    initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo,
    l_Lean_Elab_Structural_instInhabitedIndGroupInst_default,
    l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo,
};
use crate::r#gen::Lean::Expr::{l_Lean_instInhabitedExpr, l_Lean_mkSort};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_length;
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_usize_dec_eq,
};
pub static l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__0_value:
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
static mut l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Structural_instInhabitedRecArgInfo_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Structural_instInhabitedRecArgInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__9_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0_value:
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
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__1_value:
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
    m_data: [102, 110, 78, 97, 109, 101, 0],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__2_value:
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
        l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__2_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__4_value:
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
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5_value:
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
        l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        102, 105, 120, 101, 100, 80, 97, 114, 97, 109, 80, 101, 114, 109, 0,
    ],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__9_value:
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
        l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__8_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__11_value:
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
    m_data: [114, 101, 99, 65, 114, 103, 80, 111, 115, 0],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__12_value:
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
        l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__11_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__14_value:
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
    m_data: [105, 110, 100, 105, 99, 101, 115, 80, 111, 115, 0],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__15_value:
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
        l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__14_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__17_value:
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
    m_data: [105, 110, 100, 71, 114, 111, 117, 112, 73, 110, 115, 116, 0],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__18_value:
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
        l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__17_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__20_value:
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
    m_data: [105, 110, 100, 73, 100, 120, 0],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__21_value:
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
        l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__20_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__22_value:
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
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__25_value:
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
        l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__26_value:
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
        l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__22_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_instReprRecArgInfo___closed__0_value:
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
    m_fun: l_Lean_Elab_Structural_instReprRecArgInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_instReprRecArgInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_Structural_instReprRecArgInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_instReprRecArgInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2_value:
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
static mut l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = l_Lean_Elab_Structural_instInhabitedIndGroupInst_default;
    v___x_439_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_440_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__0;
    v___x_441_ = crate::leanh::lean_box(0);
    v___x_442_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_442_, 0, v___x_441_);
    crate::leanh::lean_ctor_set(v___x_442_, 1, v___x_440_);
    crate::leanh::lean_ctor_set(v___x_442_, 2, v___x_439_);
    crate::leanh::lean_ctor_set(v___x_442_, 3, v___x_440_);
    crate::leanh::lean_ctor_set(v___x_442_, 4, v___x_438_);
    crate::leanh::lean_ctor_set(v___x_442_, 5, v___x_439_);
    return v___x_442_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1_once
        ),
        _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo_default___closed__1,
    );
    return v___x_443_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo() -> *mut crate::leanh::LeanObject
{
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_444_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
    return v___x_444_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__2(
    mut v_a_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = lean_nat_to_int(v_a_445_);
    return v___x_446_;
}
pub unsafe fn l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(
    mut v_x_453_: *mut crate::leanh::LeanObject,
    mut v_x_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_453_) == 0 {
                    v___x_455_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__1;
                    return v___x_455_;
                } else {
                    v_val_456_ = crate::leanh::lean_ctor_get(v_x_453_, 0);
                    v_isSharedCheck_467_ = (!crate::leanh::lean_is_exclusive(v_x_453_)) as u8;
                    if v_isSharedCheck_467_ == 0 {
                        v___x_458_ = v_x_453_;
                        v_isShared_459_ = v_isSharedCheck_467_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_456_);
                        crate::leanh::lean_dec(v_x_453_);
                        v___x_458_ = crate::leanh::lean_box(0);
                        v_isShared_459_ = v_isSharedCheck_467_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_460_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___closed__3;
                v___x_461_ = l_Nat_reprFast(v_val_456_);
                if v_isShared_459_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_458_, 3);
                    crate::leanh::lean_ctor_set(v___x_458_, 0, v___x_461_);
                    v___x_463_ = v___x_458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_466_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_461_);
                    v___x_463_ = v_reuseFailAlloc_466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_464_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_464_, 0, v___x_460_);
                crate::leanh::lean_ctor_set(v___x_464_, 1, v___x_463_);
                v___x_465_ = l_Repr_addAppParen(v___x_464_, v_x_454_);
                return v___x_465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0___boxed(
    mut v_x_468_: *mut crate::leanh::LeanObject,
    mut v_x_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(v_x_468_, v_x_469_);
    crate::leanh::lean_dec(v_x_469_);
    return v_res_470_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1___lam__0(
    mut v___y_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_472_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_473_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(v___y_471_, v___x_472_);
    return v___x_473_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3_spec__5(
    mut v_x_474_: *mut crate::leanh::LeanObject,
    mut v_x_475_: *mut crate::leanh::LeanObject,
    mut v_x_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_481_: u8 = 0;
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_476_) == 0 {
                    crate::leanh::lean_dec(v_x_474_);
                    return v_x_475_;
                } else {
                    v_head_477_ = crate::leanh::lean_ctor_get(v_x_476_, 0);
                    v_tail_478_ = crate::leanh::lean_ctor_get(v_x_476_, 1);
                    v_isSharedCheck_489_ = (!crate::leanh::lean_is_exclusive(v_x_476_)) as u8;
                    if v_isSharedCheck_489_ == 0 {
                        v___x_480_ = v_x_476_;
                        v_isShared_481_ = v_isSharedCheck_489_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_478_);
                        crate::leanh::lean_inc(v_head_477_);
                        crate::leanh::lean_dec(v_x_476_);
                        v___x_480_ = crate::leanh::lean_box(0);
                        v_isShared_481_ = v_isSharedCheck_489_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_474_);
                if v_isShared_481_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_480_, 5);
                    crate::leanh::lean_ctor_set(v___x_480_, 1, v_x_474_);
                    crate::leanh::lean_ctor_set(v___x_480_, 0, v_x_475_);
                    v___x_483_ = v___x_480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_488_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_488_, 0, v_x_475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_488_, 1, v_x_474_);
                    v___x_483_ = v_reuseFailAlloc_488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_484_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_485_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(v_head_477_, v___x_484_);
                v___x_486_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_486_, 0, v___x_483_);
                crate::leanh::lean_ctor_set(v___x_486_, 1, v___x_485_);
                v_x_475_ = v___x_486_;
                v_x_476_ = v_tail_478_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3(
    mut v_x_490_: *mut crate::leanh::LeanObject,
    mut v_x_491_: *mut crate::leanh::LeanObject,
    mut v_x_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_497_: u8 = 0;
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_492_) == 0 {
                    crate::leanh::lean_dec(v_x_490_);
                    return v_x_491_;
                } else {
                    v_head_493_ = crate::leanh::lean_ctor_get(v_x_492_, 0);
                    v_tail_494_ = crate::leanh::lean_ctor_get(v_x_492_, 1);
                    v_isSharedCheck_505_ = (!crate::leanh::lean_is_exclusive(v_x_492_)) as u8;
                    if v_isSharedCheck_505_ == 0 {
                        v___x_496_ = v_x_492_;
                        v_isShared_497_ = v_isSharedCheck_505_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_494_);
                        crate::leanh::lean_inc(v_head_493_);
                        crate::leanh::lean_dec(v_x_492_);
                        v___x_496_ = crate::leanh::lean_box(0);
                        v_isShared_497_ = v_isSharedCheck_505_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_490_);
                if v_isShared_497_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_496_, 5);
                    crate::leanh::lean_ctor_set(v___x_496_, 1, v_x_490_);
                    crate::leanh::lean_ctor_set(v___x_496_, 0, v_x_491_);
                    v___x_499_ = v___x_496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_504_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_504_, 0, v_x_491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_504_, 1, v_x_490_);
                    v___x_499_ = v_reuseFailAlloc_504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_500_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_501_ = l_Option_repr___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__0(v_head_493_, v___x_500_);
                v___x_502_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_502_, 0, v___x_499_);
                crate::leanh::lean_ctor_set(v___x_502_, 1, v___x_501_);
                v___x_503_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3_spec__5(v_x_490_, v___x_502_, v_tail_494_);
                return v___x_503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1(
    mut v_x_506_: *mut crate::leanh::LeanObject,
    mut v_x_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_506_) == 0 {
        let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_507_);
        v___x_508_ = crate::leanh::lean_box(0);
        return v___x_508_;
    } else {
        let mut v_tail_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_509_ = crate::leanh::lean_ctor_get(v_x_506_, 1);
        if crate::leanh::lean_obj_tag(v_tail_509_) == 0 {
            let mut v_head_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_507_);
            v_head_510_ = crate::leanh::lean_ctor_get(v_x_506_, 0);
            crate::leanh::lean_inc(v_head_510_);
            crate::leanh::lean_dec_ref_known(v_x_506_, 2);
            v___x_511_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1___lam__0(v_head_510_);
            return v___x_511_;
        } else {
            let mut v_head_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_509_);
            v_head_512_ = crate::leanh::lean_ctor_get(v_x_506_, 0);
            crate::leanh::lean_inc(v_head_512_);
            crate::leanh::lean_dec_ref_known(v_x_506_, 2);
            v___x_513_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1___lam__0(v_head_512_);
            v___x_514_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1_spec__3(v_x_507_, v___x_513_, v_tail_509_);
            return v___x_514_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_523_ =
        l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__0;
    v___x_524_ = lean_string_length(v___x_523_);
    return v___x_524_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5_once), _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__5);
    v___x_526_ = lean_nat_to_int(v___x_525_);
    return v___x_526_;
}
pub unsafe fn l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0(
    mut v_xs_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: u8 = 0;
    v___x_535_ = lean_array_get_size(v_xs_534_);
    v___x_536_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_537_ = lean_nat_dec_eq(v___x_535_, v___x_536_);
    if v___x_537_ == 0 {
        let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_538_ = lean_array_to_list(v_xs_534_);
        v___x_539_ =
            l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3;
        v___x_540_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0_spec__1(v___x_538_, v___x_539_);
        v___x_541_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6);
        v___x_542_ =
            l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7;
        v___x_543_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_543_, 0, v___x_542_);
        crate::leanh::lean_ctor_set(v___x_543_, 1, v___x_540_);
        v___x_544_ =
            l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8;
        v___x_545_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_545_, 0, v___x_543_);
        crate::leanh::lean_ctor_set(v___x_545_, 1, v___x_544_);
        v___x_546_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_546_, 0, v___x_541_);
        crate::leanh::lean_ctor_set(v___x_546_, 1, v___x_545_);
        v___x_547_ = l_Std_Format_fill(v___x_546_);
        return v___x_547_;
    } else {
        let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_534_);
        v___x_548_ =
            l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10;
        return v___x_548_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6_spec__8(
    mut v_x_549_: *mut crate::leanh::LeanObject,
    mut v_x_550_: *mut crate::leanh::LeanObject,
    mut v_x_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_564_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_551_) == 0 {
                    crate::leanh::lean_dec(v_x_549_);
                    return v_x_550_;
                } else {
                    v_head_552_ = crate::leanh::lean_ctor_get(v_x_551_, 0);
                    v_tail_553_ = crate::leanh::lean_ctor_get(v_x_551_, 1);
                    v_isSharedCheck_564_ = (!crate::leanh::lean_is_exclusive(v_x_551_)) as u8;
                    if v_isSharedCheck_564_ == 0 {
                        v___x_555_ = v_x_551_;
                        v_isShared_556_ = v_isSharedCheck_564_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_553_);
                        crate::leanh::lean_inc(v_head_552_);
                        crate::leanh::lean_dec(v_x_551_);
                        v___x_555_ = crate::leanh::lean_box(0);
                        v_isShared_556_ = v_isSharedCheck_564_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_549_);
                if v_isShared_556_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_555_, 5);
                    crate::leanh::lean_ctor_set(v___x_555_, 1, v_x_549_);
                    crate::leanh::lean_ctor_set(v___x_555_, 0, v_x_550_);
                    v___x_558_ = v___x_555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_563_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_563_, 0, v_x_550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_563_, 1, v_x_549_);
                    v___x_558_ = v_reuseFailAlloc_563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_559_ = l_Nat_reprFast(v_head_552_);
                v___x_560_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_560_, 0, v___x_559_);
                v___x_561_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_561_, 0, v___x_558_);
                crate::leanh::lean_ctor_set(v___x_561_, 1, v___x_560_);
                v_x_550_ = v___x_561_;
                v_x_551_ = v_tail_553_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6(
    mut v_x_565_: *mut crate::leanh::LeanObject,
    mut v_x_566_: *mut crate::leanh::LeanObject,
    mut v_x_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_567_) == 0 {
                    crate::leanh::lean_dec(v_x_565_);
                    return v_x_566_;
                } else {
                    v_head_568_ = crate::leanh::lean_ctor_get(v_x_567_, 0);
                    v_tail_569_ = crate::leanh::lean_ctor_get(v_x_567_, 1);
                    v_isSharedCheck_580_ = (!crate::leanh::lean_is_exclusive(v_x_567_)) as u8;
                    if v_isSharedCheck_580_ == 0 {
                        v___x_571_ = v_x_567_;
                        v_isShared_572_ = v_isSharedCheck_580_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_569_);
                        crate::leanh::lean_inc(v_head_568_);
                        crate::leanh::lean_dec(v_x_567_);
                        v___x_571_ = crate::leanh::lean_box(0);
                        v_isShared_572_ = v_isSharedCheck_580_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_565_);
                if v_isShared_572_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_571_, 5);
                    crate::leanh::lean_ctor_set(v___x_571_, 1, v_x_565_);
                    crate::leanh::lean_ctor_set(v___x_571_, 0, v_x_566_);
                    v___x_574_ = v___x_571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_579_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_579_, 0, v_x_566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_579_, 1, v_x_565_);
                    v___x_574_ = v_reuseFailAlloc_579_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_575_ = l_Nat_reprFast(v_head_568_);
                v___x_576_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_575_);
                v___x_577_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_577_, 0, v___x_574_);
                crate::leanh::lean_ctor_set(v___x_577_, 1, v___x_576_);
                v___x_578_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6_spec__8(v_x_565_, v___x_577_, v_tail_569_);
                return v___x_578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3___lam__0(
    mut v___y_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = l_Nat_reprFast(v___y_581_);
    v___x_583_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_583_, 0, v___x_582_);
    return v___x_583_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3(
    mut v_x_584_: *mut crate::leanh::LeanObject,
    mut v_x_585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_584_) == 0 {
        let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_585_);
        v___x_586_ = crate::leanh::lean_box(0);
        return v___x_586_;
    } else {
        let mut v_tail_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_587_ = crate::leanh::lean_ctor_get(v_x_584_, 1);
        if crate::leanh::lean_obj_tag(v_tail_587_) == 0 {
            let mut v_head_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_585_);
            v_head_588_ = crate::leanh::lean_ctor_get(v_x_584_, 0);
            crate::leanh::lean_inc(v_head_588_);
            crate::leanh::lean_dec_ref_known(v_x_584_, 2);
            v___x_589_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3___lam__0(v_head_588_);
            return v___x_589_;
        } else {
            let mut v_head_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_587_);
            v_head_590_ = crate::leanh::lean_ctor_get(v_x_584_, 0);
            crate::leanh::lean_inc(v_head_590_);
            crate::leanh::lean_dec_ref_known(v_x_584_, 2);
            v___x_591_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3___lam__0(v_head_590_);
            v___x_592_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3_spec__6(v_x_585_, v___x_591_, v_tail_587_);
            return v___x_592_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1(
    mut v_xs_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: u8 = 0;
    v___x_594_ = lean_array_get_size(v_xs_593_);
    v___x_595_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_596_ = lean_nat_dec_eq(v___x_594_, v___x_595_);
    if v___x_596_ == 0 {
        let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_597_ = lean_array_to_list(v_xs_593_);
        v___x_598_ =
            l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__3;
        v___x_599_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1_spec__3(v___x_597_, v___x_598_);
        v___x_600_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6), core::ptr::addr_of_mut!(l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6_once), _init_l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__6);
        v___x_601_ =
            l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__7;
        v___x_602_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_602_, 0, v___x_601_);
        crate::leanh::lean_ctor_set(v___x_602_, 1, v___x_599_);
        v___x_603_ =
            l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__8;
        v___x_604_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_604_, 0, v___x_602_);
        crate::leanh::lean_ctor_set(v___x_604_, 1, v___x_603_);
        v___x_605_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_605_, 0, v___x_600_);
        crate::leanh::lean_ctor_set(v___x_605_, 1, v___x_604_);
        v___x_606_ = l_Std_Format_fill(v___x_605_);
        return v___x_606_;
    } else {
        let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_593_);
        v___x_607_ =
            l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__10;
        return v___x_607_;
    }
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_621_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_622_ = lean_nat_to_int(v___x_621_);
    return v___x_622_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_626_ = crate::leanh::lean_unsigned_to_nat(18);
    v___x_627_ = lean_nat_to_int(v___x_626_);
    return v___x_627_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_632_ = lean_nat_to_int(v___x_631_);
    return v___x_632_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_636_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_637_ = lean_nat_to_int(v___x_636_);
    return v___x_637_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_641_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_642_ = lean_nat_to_int(v___x_641_);
    return v___x_642_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_647_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__0;
    v___x_648_ = lean_string_length(v___x_647_);
    return v___x_648_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_649_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23_once
        ),
        _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__23,
    );
    v___x_650_ = lean_nat_to_int(v___x_649_);
    return v___x_650_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(
    mut v_x_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fnName_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedParamPerm_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgPos_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indGroupInst_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indIdx_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: u8 = 0;
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fnName_656_ = crate::leanh::lean_ctor_get(v_x_655_, 0);
    crate::leanh::lean_inc(v_fnName_656_);
    v_fixedParamPerm_657_ = crate::leanh::lean_ctor_get(v_x_655_, 1);
    crate::leanh::lean_inc_ref(v_fixedParamPerm_657_);
    v_recArgPos_658_ = crate::leanh::lean_ctor_get(v_x_655_, 2);
    crate::leanh::lean_inc(v_recArgPos_658_);
    v_indicesPos_659_ = crate::leanh::lean_ctor_get(v_x_655_, 3);
    crate::leanh::lean_inc_ref(v_indicesPos_659_);
    v_indGroupInst_660_ = crate::leanh::lean_ctor_get(v_x_655_, 4);
    crate::leanh::lean_inc_ref(v_indGroupInst_660_);
    v_indIdx_661_ = crate::leanh::lean_ctor_get(v_x_655_, 5);
    crate::leanh::lean_inc(v_indIdx_661_);
    crate::leanh::lean_dec_ref(v_x_655_);
    v___x_662_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__5;
    v___x_663_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__6;
    v___x_664_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__7,
    );
    v___x_665_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_666_ = l_Lean_Name_reprPrec(v_fnName_656_, v___x_665_);
    v___x_667_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_667_, 0, v___x_664_);
    crate::leanh::lean_ctor_set(v___x_667_, 1, v___x_666_);
    v___x_668_ = 0;
    v___x_669_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_669_, 0, v___x_667_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_669_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_668_,
    );
    v___x_670_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_670_, 0, v___x_663_);
    crate::leanh::lean_ctor_set(v___x_670_, 1, v___x_669_);
    v___x_671_ =
        l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0___closed__2;
    v___x_672_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_672_, 0, v___x_670_);
    crate::leanh::lean_ctor_set(v___x_672_, 1, v___x_671_);
    v___x_673_ = crate::leanh::lean_box(1);
    v___x_674_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_674_, 0, v___x_672_);
    crate::leanh::lean_ctor_set(v___x_674_, 1, v___x_673_);
    v___x_675_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__9;
    v___x_676_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_674_);
    crate::leanh::lean_ctor_set(v___x_676_, 1, v___x_675_);
    v___x_677_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_677_, 0, v___x_676_);
    crate::leanh::lean_ctor_set(v___x_677_, 1, v___x_662_);
    v___x_678_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10_once
        ),
        _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__10,
    );
    v___x_679_ = l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__0(
        v_fixedParamPerm_657_,
    );
    v___x_680_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_680_, 0, v___x_678_);
    crate::leanh::lean_ctor_set(v___x_680_, 1, v___x_679_);
    v___x_681_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_681_, 0, v___x_680_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_681_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_668_,
    );
    v___x_682_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_682_, 0, v___x_677_);
    crate::leanh::lean_ctor_set(v___x_682_, 1, v___x_681_);
    v___x_683_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_683_, 0, v___x_682_);
    crate::leanh::lean_ctor_set(v___x_683_, 1, v___x_671_);
    v___x_684_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_684_, 0, v___x_683_);
    crate::leanh::lean_ctor_set(v___x_684_, 1, v___x_673_);
    v___x_685_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__12;
    v___x_686_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_684_);
    crate::leanh::lean_ctor_set(v___x_686_, 1, v___x_685_);
    v___x_687_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_687_, 0, v___x_686_);
    crate::leanh::lean_ctor_set(v___x_687_, 1, v___x_662_);
    v___x_688_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13_once
        ),
        _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__13,
    );
    v___x_689_ = l_Nat_reprFast(v_recArgPos_658_);
    v___x_690_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_690_, 0, v___x_689_);
    v___x_691_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_691_, 0, v___x_688_);
    crate::leanh::lean_ctor_set(v___x_691_, 1, v___x_690_);
    v___x_692_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_692_, 0, v___x_691_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_692_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_668_,
    );
    v___x_693_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_693_, 0, v___x_687_);
    crate::leanh::lean_ctor_set(v___x_693_, 1, v___x_692_);
    v___x_694_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_694_, 0, v___x_693_);
    crate::leanh::lean_ctor_set(v___x_694_, 1, v___x_671_);
    v___x_695_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_695_, 0, v___x_694_);
    crate::leanh::lean_ctor_set(v___x_695_, 1, v___x_673_);
    v___x_696_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__15;
    v___x_697_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_697_, 0, v___x_695_);
    crate::leanh::lean_ctor_set(v___x_697_, 1, v___x_696_);
    v___x_698_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_698_, 0, v___x_697_);
    crate::leanh::lean_ctor_set(v___x_698_, 1, v___x_662_);
    v___x_699_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16_once
        ),
        _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__16,
    );
    v___x_700_ = l_Array_repr___at___00Lean_Elab_Structural_instReprRecArgInfo_repr_spec__1(
        v_indicesPos_659_,
    );
    v___x_701_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_701_, 0, v___x_699_);
    crate::leanh::lean_ctor_set(v___x_701_, 1, v___x_700_);
    v___x_702_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_702_, 0, v___x_701_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_702_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_668_,
    );
    v___x_703_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_703_, 0, v___x_698_);
    crate::leanh::lean_ctor_set(v___x_703_, 1, v___x_702_);
    v___x_704_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_704_, 0, v___x_703_);
    crate::leanh::lean_ctor_set(v___x_704_, 1, v___x_671_);
    v___x_705_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_705_, 0, v___x_704_);
    crate::leanh::lean_ctor_set(v___x_705_, 1, v___x_673_);
    v___x_706_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__18;
    v___x_707_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_707_, 0, v___x_705_);
    crate::leanh::lean_ctor_set(v___x_707_, 1, v___x_706_);
    v___x_708_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_708_, 0, v___x_707_);
    crate::leanh::lean_ctor_set(v___x_708_, 1, v___x_662_);
    v___x_709_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19_once
        ),
        _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__19,
    );
    v___x_710_ = l_Lean_Elab_Structural_instReprIndGroupInst_repr___redArg(v_indGroupInst_660_);
    v___x_711_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_711_, 0, v___x_709_);
    crate::leanh::lean_ctor_set(v___x_711_, 1, v___x_710_);
    v___x_712_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_712_, 0, v___x_711_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_712_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_668_,
    );
    v___x_713_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_713_, 0, v___x_708_);
    crate::leanh::lean_ctor_set(v___x_713_, 1, v___x_712_);
    v___x_714_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_714_, 0, v___x_713_);
    crate::leanh::lean_ctor_set(v___x_714_, 1, v___x_671_);
    v___x_715_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_715_, 0, v___x_714_);
    crate::leanh::lean_ctor_set(v___x_715_, 1, v___x_673_);
    v___x_716_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__21;
    v___x_717_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_717_, 0, v___x_715_);
    crate::leanh::lean_ctor_set(v___x_717_, 1, v___x_716_);
    v___x_718_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_718_, 0, v___x_717_);
    crate::leanh::lean_ctor_set(v___x_718_, 1, v___x_662_);
    v___x_719_ = l_Nat_reprFast(v_indIdx_661_);
    v___x_720_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_720_, 0, v___x_719_);
    v___x_721_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_721_, 0, v___x_664_);
    crate::leanh::lean_ctor_set(v___x_721_, 1, v___x_720_);
    v___x_722_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_722_, 0, v___x_721_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_722_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_668_,
    );
    v___x_723_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_723_, 0, v___x_718_);
    crate::leanh::lean_ctor_set(v___x_723_, 1, v___x_722_);
    v___x_724_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24_once
        ),
        _init_l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__24,
    );
    v___x_725_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__25;
    v___x_726_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_726_, 0, v___x_725_);
    crate::leanh::lean_ctor_set(v___x_726_, 1, v___x_723_);
    v___x_727_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg___closed__26;
    v___x_728_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_728_, 0, v___x_726_);
    crate::leanh::lean_ctor_set(v___x_728_, 1, v___x_727_);
    v___x_729_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_729_, 0, v___x_724_);
    crate::leanh::lean_ctor_set(v___x_729_, 1, v___x_728_);
    v___x_730_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_730_, 0, v___x_729_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_730_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_668_,
    );
    return v___x_730_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprRecArgInfo_repr(
    mut v_x_731_: *mut crate::leanh::LeanObject,
    mut v_prec_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_x_731_);
    return v___x_733_;
}
pub unsafe fn l_Lean_Elab_Structural_instReprRecArgInfo_repr___boxed(
    mut v_x_734_: *mut crate::leanh::LeanObject,
    mut v_prec_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_736_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr(v_x_734_, v_prec_735_);
    crate::leanh::lean_dec(v_prec_735_);
    return v_res_736_;
}
pub unsafe fn l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(
    mut v_info_739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_recArgPos_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_recArgPos_740_ = crate::leanh::lean_ctor_get(v_info_739_, 2);
    crate::leanh::lean_inc(v_recArgPos_740_);
    v_indicesPos_741_ = crate::leanh::lean_ctor_get(v_info_739_, 3);
    crate::leanh::lean_inc_ref(v_indicesPos_741_);
    crate::leanh::lean_dec_ref(v_info_739_);
    v___x_742_ = lean_array_push(v_indicesPos_741_, v_recArgPos_740_);
    return v___x_742_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0(
    mut v_a_743_: *mut crate::leanh::LeanObject,
    mut v_as_744_: *mut crate::leanh::LeanObject,
    mut v_i_745_: usize,
    mut v_stop_746_: usize,
) -> u8 {
    let mut v___x_747_: u8 = 0;
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: u8 = 0;
    let mut v___x_750_: usize = 0;
    let mut v___x_751_: usize = 0;
    let mut v___x_753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_747_ = lean_usize_dec_eq(v_i_745_, v_stop_746_);
                if v___x_747_ == 0 {
                    v___x_748_ = lean_array_uget_borrowed(v_as_744_, v_i_745_);
                    v___x_749_ = lean_nat_dec_eq(v_a_743_, v___x_748_);
                    if v___x_749_ == 0 {
                        v___x_750_ = 1usize;
                        v___x_751_ = lean_usize_add(v_i_745_, v___x_750_);
                        v_i_745_ = v___x_751_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_749_;
                    }
                } else {
                    v___x_753_ = 0;
                    return v___x_753_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0___boxed(
    mut v_a_754_: *mut crate::leanh::LeanObject,
    mut v_as_755_: *mut crate::leanh::LeanObject,
    mut v_i_756_: *mut crate::leanh::LeanObject,
    mut v_stop_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_758_: usize = 0;
    let mut v_stop_boxed_759_: usize = 0;
    let mut v_res_760_: u8 = 0;
    let mut v_r_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_758_ = crate::leanh::lean_unbox_usize(v_i_756_);
    crate::leanh::lean_dec(v_i_756_);
    v_stop_boxed_759_ = crate::leanh::lean_unbox_usize(v_stop_757_);
    crate::leanh::lean_dec(v_stop_757_);
    v_res_760_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0(v_a_754_, v_as_755_, v_i_boxed_758_, v_stop_boxed_759_);
    crate::leanh::lean_dec_ref(v_as_755_);
    crate::leanh::lean_dec(v_a_754_);
    v_r_761_ = crate::leanh::lean_box((v_res_760_) as usize);
    return v_r_761_;
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0(
    mut v_as_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: u8 = 0;
    v___x_764_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_765_ = lean_array_get_size(v_as_762_);
    v___x_766_ = lean_nat_dec_lt(v___x_764_, v___x_765_);
    if v___x_766_ == 0 {
        return v___x_766_;
    } else {
        if v___x_766_ == 0 {
            return v___x_766_;
        } else {
            let mut v___x_767_: usize = 0;
            let mut v___x_768_: usize = 0;
            let mut v___x_769_: u8 = 0;
            v___x_767_ = 0usize;
            v___x_768_ = lean_usize_of_nat(v___x_765_);
            v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0_spec__0(v_a_763_, v_as_762_, v___x_767_, v___x_768_);
            return v___x_769_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0___boxed(
    mut v_as_770_: *mut crate::leanh::LeanObject,
    mut v_a_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_772_: u8 = 0;
    let mut v_r_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_772_ = l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0(
        v_as_770_, v_a_771_,
    );
    crate::leanh::lean_dec(v_a_771_);
    crate::leanh::lean_dec_ref(v_as_770_);
    v_r_773_ = crate::leanh::lean_box((v_res_772_) as usize);
    return v_r_773_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg(
    mut v_upperBound_774_: *mut crate::leanh::LeanObject,
    mut v_indexMajorPos_775_: *mut crate::leanh::LeanObject,
    mut v___x_776_: *mut crate::leanh::LeanObject,
    mut v_xs_777_: *mut crate::leanh::LeanObject,
    mut v_a_778_: *mut crate::leanh::LeanObject,
    mut v_b_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: u8 = 0;
    let mut v___x_786_: u8 = 0;
    let mut v___x_787_: u8 = 0;
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_785_ = lean_nat_dec_lt(v_a_778_, v_upperBound_774_);
                if v___x_785_ == 0 {
                    crate::leanh::lean_dec(v_a_778_);
                    return v_b_779_;
                } else {
                    v___x_786_ = l_Array_contains___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__0(v_indexMajorPos_775_, v_a_778_);
                    if v___x_786_ == 0 {
                        v___x_787_ = l_Lean_Elab_FixedParamPerm_isFixed(v___x_776_, v_a_778_);
                        if v___x_787_ == 0 {
                            v___x_788_ = lean_array_fget_borrowed(v_xs_777_, v_a_778_);
                            crate::leanh::lean_inc(v___x_788_);
                            v___x_789_ = lean_array_push(v_b_779_, v___x_788_);
                            v_a_781_ = v___x_789_;
                            state = 1;
                            continue;
                        } else {
                            v_a_781_ = v_b_779_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_781_ = v_b_779_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_782_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_783_ = lean_nat_add(v_a_778_, v___x_782_);
                crate::leanh::lean_dec(v_a_778_);
                v_a_778_ = v___x_783_;
                v_b_779_ = v_a_781_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg___boxed(
    mut v_upperBound_790_: *mut crate::leanh::LeanObject,
    mut v_indexMajorPos_791_: *mut crate::leanh::LeanObject,
    mut v___x_792_: *mut crate::leanh::LeanObject,
    mut v_xs_793_: *mut crate::leanh::LeanObject,
    mut v_a_794_: *mut crate::leanh::LeanObject,
    mut v_b_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_796_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg(v_upperBound_790_, v_indexMajorPos_791_, v___x_792_, v_xs_793_, v_a_794_, v_b_795_);
    crate::leanh::lean_dec_ref(v_xs_793_);
    crate::leanh::lean_dec_ref(v___x_792_);
    crate::leanh::lean_dec_ref(v_indexMajorPos_791_);
    crate::leanh::lean_dec(v_upperBound_790_);
    return v_res_796_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1(
    mut v_xs_797_: *mut crate::leanh::LeanObject,
    mut v_as_798_: *mut crate::leanh::LeanObject,
    mut v_sz_799_: usize,
    mut v_i_800_: usize,
    mut v_b_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_802_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: usize = 0;
    let mut v___x_808_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_802_ = lean_usize_dec_lt(v_i_800_, v_sz_799_);
                if v___x_802_ == 0 {
                    return v_b_801_;
                } else {
                    v___x_803_ = l_Lean_instInhabitedExpr;
                    v_a_804_ = lean_array_uget_borrowed(v_as_798_, v_i_800_);
                    v___x_805_ = lean_array_get_borrowed(v___x_803_, v_xs_797_, v_a_804_);
                    crate::leanh::lean_inc(v___x_805_);
                    v___x_806_ = lean_array_push(v_b_801_, v___x_805_);
                    v___x_807_ = 1usize;
                    v___x_808_ = lean_usize_add(v_i_800_, v___x_807_);
                    v_i_800_ = v___x_808_;
                    v_b_801_ = v___x_806_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1___boxed(
    mut v_xs_810_: *mut crate::leanh::LeanObject,
    mut v_as_811_: *mut crate::leanh::LeanObject,
    mut v_sz_812_: *mut crate::leanh::LeanObject,
    mut v_i_813_: *mut crate::leanh::LeanObject,
    mut v_b_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_815_: usize = 0;
    let mut v_i_boxed_816_: usize = 0;
    let mut v_res_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_815_ = crate::leanh::lean_unbox_usize(v_sz_812_);
    crate::leanh::lean_dec(v_sz_812_);
    v_i_boxed_816_ = crate::leanh::lean_unbox_usize(v_i_813_);
    crate::leanh::lean_dec(v_i_813_);
    v_res_817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1(v_xs_810_, v_as_811_, v_sz_boxed_815_, v_i_boxed_816_, v_b_814_);
    crate::leanh::lean_dec_ref(v_as_811_);
    crate::leanh::lean_dec_ref(v_xs_810_);
    return v_res_817_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_819_ = l_Lean_Level_ofNat(v___x_818_);
    return v___x_819_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_820_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0_once
        ),
        _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__0,
    );
    v___x_821_ = l_Lean_mkSort(v___x_820_);
    return v___x_821_;
}
pub unsafe fn l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(
    mut v_info_824_: *mut crate::leanh::LeanObject,
    mut v_xs_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fixedParamPerm_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgPos_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexMajorPos_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_835_: usize = 0;
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indexMajorArgs_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: usize = 0;
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fixedParamPerm_826_ = crate::leanh::lean_ctor_get(v_info_824_, 1);
    crate::leanh::lean_inc_ref_n(v_fixedParamPerm_826_, 2);
    v_recArgPos_827_ = crate::leanh::lean_ctor_get(v_info_824_, 2);
    crate::leanh::lean_inc(v_recArgPos_827_);
    v_indicesPos_828_ = crate::leanh::lean_ctor_get(v_info_824_, 3);
    crate::leanh::lean_inc_ref(v_indicesPos_828_);
    crate::leanh::lean_dec_ref(v_info_824_);
    v___x_829_ = l_Lean_Elab_FixedParamPerm_numFixed(v_fixedParamPerm_826_);
    v___x_830_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_831_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1_once
        ),
        _init_l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__1,
    );
    v___x_832_ = lean_mk_array(v___x_829_, v___x_831_);
    v_xs_833_ =
        l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_fixedParamPerm_826_, v___x_832_, v_xs_825_);
    crate::leanh::lean_dec_ref(v___x_832_);
    v_indexMajorPos_834_ = lean_array_push(v_indicesPos_828_, v_recArgPos_827_);
    v_sz_835_ = lean_array_size(v_indexMajorPos_834_);
    v___x_836_ = lean_array_get_size(v_xs_833_);
    v_indexMajorArgs_837_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor___closed__2;
    v___x_838_ = 0usize;
    v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__1(v_xs_833_, v_indexMajorPos_834_, v_sz_835_, v___x_838_, v_indexMajorArgs_837_);
    v___x_840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg(v___x_836_, v_indexMajorPos_834_, v_fixedParamPerm_826_, v_xs_833_, v___x_830_, v_indexMajorArgs_837_);
    crate::leanh::lean_dec_ref(v_xs_833_);
    crate::leanh::lean_dec_ref(v_fixedParamPerm_826_);
    crate::leanh::lean_dec_ref(v_indexMajorPos_834_);
    v___x_841_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_841_, 0, v___x_839_);
    crate::leanh::lean_ctor_set(v___x_841_, 1, v___x_840_);
    return v___x_841_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2(
    mut v_upperBound_842_: *mut crate::leanh::LeanObject,
    mut v_indexMajorPos_843_: *mut crate::leanh::LeanObject,
    mut v___x_844_: *mut crate::leanh::LeanObject,
    mut v_xs_845_: *mut crate::leanh::LeanObject,
    mut v_inst_846_: *mut crate::leanh::LeanObject,
    mut v_R_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
    mut v_b_849_: *mut crate::leanh::LeanObject,
    mut v_c_850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___redArg(v_upperBound_842_, v_indexMajorPos_843_, v___x_844_, v_xs_845_, v_a_848_, v_b_849_);
    return v___x_851_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2___boxed(
    mut v_upperBound_852_: *mut crate::leanh::LeanObject,
    mut v_indexMajorPos_853_: *mut crate::leanh::LeanObject,
    mut v___x_854_: *mut crate::leanh::LeanObject,
    mut v_xs_855_: *mut crate::leanh::LeanObject,
    mut v_inst_856_: *mut crate::leanh::LeanObject,
    mut v_R_857_: *mut crate::leanh::LeanObject,
    mut v_a_858_: *mut crate::leanh::LeanObject,
    mut v_b_859_: *mut crate::leanh::LeanObject,
    mut v_c_860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_RecArgInfo_pickIndicesMajor_spec__2(v_upperBound_852_, v_indexMajorPos_853_, v___x_854_, v_xs_855_, v_inst_856_, v_R_857_, v_a_858_, v_b_859_, v_c_860_);
    crate::leanh::lean_dec_ref(v_xs_855_);
    crate::leanh::lean_dec_ref(v___x_854_);
    crate::leanh::lean_dec_ref(v_indexMajorPos_853_);
    crate::leanh::lean_dec(v_upperBound_852_);
    return v_res_861_;
}
pub unsafe fn l_Lean_Elab_Structural_RecArgInfo_indName_x21(
    mut v_info_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_indGroupInst_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIndGroupInfo_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indIdx_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_indGroupInst_863_ = crate::leanh::lean_ctor_get(v_info_862_, 4);
    v_toIndGroupInfo_864_ = crate::leanh::lean_ctor_get(v_indGroupInst_863_, 0);
    v_indIdx_865_ = crate::leanh::lean_ctor_get(v_info_862_, 5);
    v_all_866_ = crate::leanh::lean_ctor_get(v_toIndGroupInfo_864_, 0);
    v___x_867_ = crate::leanh::lean_box(0);
    v___x_868_ = lean_array_get_borrowed(v___x_867_, v_all_866_, v_indIdx_865_);
    crate::leanh::lean_inc(v___x_868_);
    return v___x_868_;
}
pub unsafe fn l_Lean_Elab_Structural_RecArgInfo_indName_x21___boxed(
    mut v_info_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_870_ = l_Lean_Elab_Structural_RecArgInfo_indName_x21(v_info_869_);
    crate::leanh::lean_dec_ref(v_info_869_);
    return v_res_870_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_Structural_instInhabitedRecArgInfo_default =
        _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedRecArgInfo_default);
    l_Lean_Elab_Structural_instInhabitedRecArgInfo =
        _init_l_Lean_Elab_Structural_instInhabitedRecArgInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedRecArgInfo);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_IndGroupInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
}

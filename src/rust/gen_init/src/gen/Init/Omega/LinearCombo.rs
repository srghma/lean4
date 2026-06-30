// Lean compiler output
// Module: Init.Omega.LinearCombo
// Imports: Init.Omega.Coeffs Init.Data.Int.Lemmas Init.Data.ToString.Macro Init.RCases
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_int_sub,
    lean_nat_abs, lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_nat_to_int, lean_string_append,
    lean_string_length,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Int::Basic::l_Int_instDecidableEq___boxed;
use crate::r#gen::Init::Data::Int::Lemmas::{
    initialize_Init_Data_Int_Lemmas, runtime_initialize_Init_Data_Int_Lemmas,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_mapTR_loop___redArg, l_List_reverse___redArg, l_List_zipIdx___redArg,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Data::String::Bootstrap::l_String_Internal_append___boxed;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Omega::Coeffs::{
    initialize_Init_Omega_Coeffs, runtime_initialize_Init_Omega_Coeffs,
};
use crate::r#gen::Init::Omega::IntList::{
    l_Lean_Omega_IntList_dot, l_Lean_Omega_IntList_neg, l_Lean_Omega_IntList_set,
    l_Lean_Omega_IntList_smul, l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0,
    l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0,
};
use crate::r#gen::Init::Prelude::{l_List_lengthTR___redArg, l_instDecidableEqList___redArg};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
pub static l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString___closed__0_value:
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
    m_fun: l_String_Internal_append___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_LinearCombo_0__Lean_Omega_instAppendString___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [45, 0]};
static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___closed__0_value:
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
    m_fun: l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___closed__0_value:
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
    m_fun: l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__3_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject] };
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__6_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject] };
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject] };
static mut l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0_value:
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
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__1_value:
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
    m_data: [99, 111, 110, 115, 116, 0],
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__4_value:
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
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__8_value:
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
    m_data: [99, 111, 101, 102, 102, 115, 0],
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__11_value:
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
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_instReprLinearCombo___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_instReprLinearCombo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_instReprLinearCombo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Omega_instReprLinearCombo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_instReprLinearCombo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0_value:
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
static mut l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0_value:
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
    m_data: [32, 43, 32, 0],
};
static mut l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1_value:
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
    m_data: [32, 42, 32, 120, 0],
};
static mut l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Omega_LinearCombo_instToString___private__1___closed__0_value:
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
    m_fun: l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Omega_LinearCombo_instToString___private__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instToString___private__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_LinearCombo_instToString___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Omega_LinearCombo_instToString___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Omega_LinearCombo_instToString___private__1___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Omega_LinearCombo_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Omega_LinearCombo_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instToString___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Omega_LinearCombo_instInhabited___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Omega_LinearCombo_instInhabited___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Omega_LinearCombo_instInhabited___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Omega_LinearCombo_instInhabited___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Omega_LinearCombo_instInhabited: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Omega_LinearCombo_instAdd___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_LinearCombo_add as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_LinearCombo_instAdd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instAdd___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Omega_LinearCombo_instAdd: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instAdd___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_LinearCombo_instSub___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_LinearCombo_sub as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_LinearCombo_instSub___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instSub___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Omega_LinearCombo_instSub: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instSub___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_LinearCombo_instNeg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_LinearCombo_neg as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_LinearCombo_instNeg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instNeg___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Omega_LinearCombo_instNeg: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instNeg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Omega_LinearCombo_instHMulInt___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Omega_LinearCombo_instHMulInt___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Omega_LinearCombo_instHMulInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instHMulInt___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Omega_LinearCombo_instHMulInt: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_LinearCombo_instHMulInt___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v_natZero_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_590_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_591_ = lean_nat_to_int(v_natZero_590_);
    return v_intZero_591_;
}
pub unsafe fn l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0(
    mut v_x_593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_595_: u8 = 0;
    v_intZero_594_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
    v_isNeg_595_ = lean_int_dec_lt(v_x_593_, v_intZero_594_);
    if v_isNeg_595_ == 0 {
        let mut v_a_596_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_596_ = lean_nat_abs(v_x_593_);
        v___x_597_ = l_Nat_reprFast(v_a_596_);
        return v___x_597_;
    } else {
        let mut v_abs_598_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_600_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_abs_598_ = lean_nat_abs(v_x_593_);
        v_one_599_ = leanh::lean_unsigned_to_nat(1);
        v_a_600_ = lean_nat_sub(v_abs_598_, v_one_599_);
        leanh::lean_dec(v_abs_598_);
        v___x_601_ =
            l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
        v___x_602_ = lean_nat_add(v_a_600_, v_one_599_);
        leanh::lean_dec(v_a_600_);
        v___x_603_ = l_Nat_reprFast(v___x_602_);
        v___x_604_ = lean_string_append(v___x_601_, v___x_603_);
        leanh::lean_dec_ref(v___x_603_);
        return v___x_604_;
    }
}
pub unsafe fn l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___boxed(
    mut v_x_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_606_ =
        l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0(v_x_605_);
    leanh::lean_dec(v_x_605_);
    return v_res_606_;
}
pub unsafe fn l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0(
    mut v_i_609_: *mut leanh::LeanObject,
    mut v_prec_610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: u8 = 0;
    let mut v_a_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_615_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v___x_616_ = lean_int_dec_lt(v_i_609_, v___x_615_);
                if v___x_616_ == 0 {
                    if v___x_616_ == 0 {
                        v_a_617_ = lean_nat_abs(v_i_609_);
                        v___x_618_ = l_Nat_reprFast(v_a_617_);
                        v___x_619_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_619_, 0, v___x_618_);
                        return v___x_619_;
                    } else {
                        v_abs_620_ = lean_nat_abs(v_i_609_);
                        v_one_621_ = leanh::lean_unsigned_to_nat(1);
                        v_a_622_ = lean_nat_sub(v_abs_620_, v_one_621_);
                        leanh::lean_dec(v_abs_620_);
                        v___x_623_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_624_ = lean_nat_add(v_a_622_, v_one_621_);
                        leanh::lean_dec(v_a_622_);
                        v___x_625_ = l_Nat_reprFast(v___x_624_);
                        v___x_626_ = lean_string_append(v___x_623_, v___x_625_);
                        leanh::lean_dec_ref(v___x_625_);
                        v___x_627_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_627_, 0, v___x_626_);
                        return v___x_627_;
                    }
                } else {
                    if v___x_616_ == 0 {
                        v_a_628_ = lean_nat_abs(v_i_609_);
                        v___x_629_ = l_Nat_reprFast(v_a_628_);
                        v___y_612_ = v___x_629_;
                        state = 1;
                        continue;
                    } else {
                        v_abs_630_ = lean_nat_abs(v_i_609_);
                        v_one_631_ = leanh::lean_unsigned_to_nat(1);
                        v_a_632_ = lean_nat_sub(v_abs_630_, v_one_631_);
                        leanh::lean_dec(v_abs_630_);
                        v___x_633_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_634_ = lean_nat_add(v_a_632_, v_one_631_);
                        leanh::lean_dec(v_a_632_);
                        v___x_635_ = l_Nat_reprFast(v___x_634_);
                        v___x_636_ = lean_string_append(v___x_633_, v___x_635_);
                        leanh::lean_dec_ref(v___x_635_);
                        v___y_612_ = v___x_636_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_613_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_613_, 0, v___y_612_);
                v___x_614_ = l_Repr_addAppParen(v___x_613_, v_prec_610_);
                return v___x_614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0___boxed(
    mut v_i_637_: *mut leanh::LeanObject,
    mut v_prec_638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_639_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instReprInt___lam__0(
        v_i_637_,
        v_prec_638_,
    );
    leanh::lean_dec(v_prec_638_);
    leanh::lean_dec(v_i_637_);
    return v_res_639_;
}
pub unsafe fn l_Lean_Omega_instDecidableEqLinearCombo_decEq(
    mut v_x_642_: *mut leanh::LeanObject,
    mut v_x_643_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_const_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_const_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: u8 = 0;
    v_const_644_ = leanh::lean_ctor_get(v_x_642_, 0);
    leanh::lean_inc(v_const_644_);
    v_coeffs_645_ = leanh::lean_ctor_get(v_x_642_, 1);
    leanh::lean_inc(v_coeffs_645_);
    leanh::lean_dec_ref(v_x_642_);
    v_const_646_ = leanh::lean_ctor_get(v_x_643_, 0);
    leanh::lean_inc(v_const_646_);
    v_coeffs_647_ = leanh::lean_ctor_get(v_x_643_, 1);
    leanh::lean_inc(v_coeffs_647_);
    leanh::lean_dec_ref(v_x_643_);
    v___x_648_ = lean_int_dec_eq(v_const_644_, v_const_646_);
    leanh::lean_dec(v_const_646_);
    leanh::lean_dec(v_const_644_);
    if v___x_648_ == 0 {
        leanh::lean_dec(v_coeffs_647_);
        leanh::lean_dec(v_coeffs_645_);
        return v___x_648_;
    } else {
        let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_650_: u8 = 0;
        v___x_649_ = leanh::lean_alloc_closure(
            l_Int_instDecidableEq___boxed as *mut core::ffi::c_void,
            2,
            0,
        );
        v___x_650_ = l_instDecidableEqList___redArg(v___x_649_, v_coeffs_645_, v_coeffs_647_);
        return v___x_650_;
    }
}
pub unsafe fn l_Lean_Omega_instDecidableEqLinearCombo_decEq___boxed(
    mut v_x_651_: *mut leanh::LeanObject,
    mut v_x_652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_653_: u8 = 0;
    let mut v_r_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_653_ = l_Lean_Omega_instDecidableEqLinearCombo_decEq(v_x_651_, v_x_652_);
    v_r_654_ = leanh::lean_box((v_res_653_) as usize);
    return v_r_654_;
}
pub unsafe fn l_Lean_Omega_instDecidableEqLinearCombo(
    mut v_x_655_: *mut leanh::LeanObject,
    mut v_x_656_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_657_: u8 = 0;
    v___x_657_ = l_Lean_Omega_instDecidableEqLinearCombo_decEq(v_x_655_, v_x_656_);
    return v___x_657_;
}
pub unsafe fn l_Lean_Omega_instDecidableEqLinearCombo___boxed(
    mut v_x_658_: *mut leanh::LeanObject,
    mut v_x_659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_660_: u8 = 0;
    let mut v_r_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lean_Omega_instDecidableEqLinearCombo(v_x_658_, v_x_659_);
    v_r_661_ = leanh::lean_box((v_res_660_) as usize);
    return v_r_661_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Omega_instReprLinearCombo_repr_spec__1(
    mut v_a_662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_663_ = lean_nat_to_int(v_a_662_);
    return v___x_663_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_664_: *mut leanh::LeanObject,
    mut v_x_665_: *mut leanh::LeanObject,
    mut v_x_666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_671_: u8 = 0;
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u8 = 0;
    let mut v_a_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_666_) == 0 {
                    leanh::lean_dec(v_x_664_);
                    return v_x_665_;
                } else {
                    v_head_667_ = leanh::lean_ctor_get(v_x_666_, 0);
                    v_tail_668_ = leanh::lean_ctor_get(v_x_666_, 1);
                    v_isSharedCheck_708_ = (!leanh::lean_is_exclusive(v_x_666_)) as u8;
                    if v_isSharedCheck_708_ == 0 {
                        v___x_670_ = v_x_666_;
                        v_isShared_671_ = v_isSharedCheck_708_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_668_);
                        leanh::lean_inc(v_head_667_);
                        leanh::lean_dec(v_x_666_);
                        v___x_670_ = leanh::lean_box(0);
                        v_isShared_671_ = v_isSharedCheck_708_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_664_);
                if v_isShared_671_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_670_, 5);
                    leanh::lean_ctor_set(v___x_670_, 1, v_x_664_);
                    leanh::lean_ctor_set(v___x_670_, 0, v_x_665_);
                    v___x_673_ = v___x_670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v_x_665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_707_, 1, v_x_664_);
                    v___x_673_ = v_reuseFailAlloc_707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_674_ = leanh::lean_unsigned_to_nat(0);
                v___x_681_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v___x_682_ = lean_int_dec_lt(v_head_667_, v___x_681_);
                if v___x_682_ == 0 {
                    if v___x_682_ == 0 {
                        v_a_683_ = lean_nat_abs(v_head_667_);
                        leanh::lean_dec(v_head_667_);
                        v___x_684_ = l_Nat_reprFast(v_a_683_);
                        v___x_685_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_685_, 0, v___x_684_);
                        v___x_686_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_686_, 0, v___x_673_);
                        leanh::lean_ctor_set(v___x_686_, 1, v___x_685_);
                        v_x_665_ = v___x_686_;
                        v_x_666_ = v_tail_668_;
                        state = 0;
                        continue;
                    } else {
                        v_abs_688_ = lean_nat_abs(v_head_667_);
                        leanh::lean_dec(v_head_667_);
                        v_one_689_ = leanh::lean_unsigned_to_nat(1);
                        v_a_690_ = lean_nat_sub(v_abs_688_, v_one_689_);
                        leanh::lean_dec(v_abs_688_);
                        v___x_691_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_692_ = lean_nat_add(v_a_690_, v_one_689_);
                        leanh::lean_dec(v_a_690_);
                        v___x_693_ = l_Nat_reprFast(v___x_692_);
                        v___x_694_ = lean_string_append(v___x_691_, v___x_693_);
                        leanh::lean_dec_ref(v___x_693_);
                        v___x_695_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_695_, 0, v___x_694_);
                        v___x_696_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_696_, 0, v___x_673_);
                        leanh::lean_ctor_set(v___x_696_, 1, v___x_695_);
                        v_x_665_ = v___x_696_;
                        v_x_666_ = v_tail_668_;
                        state = 0;
                        continue;
                    }
                } else {
                    if v___x_682_ == 0 {
                        v_a_698_ = lean_nat_abs(v_head_667_);
                        leanh::lean_dec(v_head_667_);
                        v___x_699_ = l_Nat_reprFast(v_a_698_);
                        v___y_676_ = v___x_699_;
                        state = 3;
                        continue;
                    } else {
                        v_abs_700_ = lean_nat_abs(v_head_667_);
                        leanh::lean_dec(v_head_667_);
                        v_one_701_ = leanh::lean_unsigned_to_nat(1);
                        v_a_702_ = lean_nat_sub(v_abs_700_, v_one_701_);
                        leanh::lean_dec(v_abs_700_);
                        v___x_703_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_704_ = lean_nat_add(v_a_702_, v_one_701_);
                        leanh::lean_dec(v_a_702_);
                        v___x_705_ = l_Nat_reprFast(v___x_704_);
                        v___x_706_ = lean_string_append(v___x_703_, v___x_705_);
                        leanh::lean_dec_ref(v___x_705_);
                        v___y_676_ = v___x_706_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_677_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_677_, 0, v___y_676_);
                v___x_678_ = l_Repr_addAppParen(v___x_677_, v___x_674_);
                v___x_679_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_679_, 0, v___x_673_);
                leanh::lean_ctor_set(v___x_679_, 1, v___x_678_);
                v_x_665_ = v___x_679_;
                v_x_666_ = v_tail_668_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2(
    mut v_x_709_: *mut leanh::LeanObject,
    mut v_x_710_: *mut leanh::LeanObject,
    mut v_x_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_716_: u8 = 0;
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u8 = 0;
    let mut v_a_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_711_) == 0 {
                    leanh::lean_dec(v_x_709_);
                    return v_x_710_;
                } else {
                    v_head_712_ = leanh::lean_ctor_get(v_x_711_, 0);
                    v_tail_713_ = leanh::lean_ctor_get(v_x_711_, 1);
                    v_isSharedCheck_753_ = (!leanh::lean_is_exclusive(v_x_711_)) as u8;
                    if v_isSharedCheck_753_ == 0 {
                        v___x_715_ = v_x_711_;
                        v_isShared_716_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_713_);
                        leanh::lean_inc(v_head_712_);
                        leanh::lean_dec(v_x_711_);
                        v___x_715_ = leanh::lean_box(0);
                        v_isShared_716_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_709_);
                if v_isShared_716_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_715_, 5);
                    leanh::lean_ctor_set(v___x_715_, 1, v_x_709_);
                    leanh::lean_ctor_set(v___x_715_, 0, v_x_710_);
                    v___x_718_ = v___x_715_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_752_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_752_, 0, v_x_710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_752_, 1, v_x_709_);
                    v___x_718_ = v_reuseFailAlloc_752_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_719_ = leanh::lean_unsigned_to_nat(0);
                v___x_726_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v___x_727_ = lean_int_dec_lt(v_head_712_, v___x_726_);
                if v___x_727_ == 0 {
                    if v___x_727_ == 0 {
                        v_a_728_ = lean_nat_abs(v_head_712_);
                        leanh::lean_dec(v_head_712_);
                        v___x_729_ = l_Nat_reprFast(v_a_728_);
                        v___x_730_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_730_, 0, v___x_729_);
                        v___x_731_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_731_, 0, v___x_718_);
                        leanh::lean_ctor_set(v___x_731_, 1, v___x_730_);
                        v___x_732_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_709_, v___x_731_, v_tail_713_);
                        return v___x_732_;
                    } else {
                        v_abs_733_ = lean_nat_abs(v_head_712_);
                        leanh::lean_dec(v_head_712_);
                        v_one_734_ = leanh::lean_unsigned_to_nat(1);
                        v_a_735_ = lean_nat_sub(v_abs_733_, v_one_734_);
                        leanh::lean_dec(v_abs_733_);
                        v___x_736_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_737_ = lean_nat_add(v_a_735_, v_one_734_);
                        leanh::lean_dec(v_a_735_);
                        v___x_738_ = l_Nat_reprFast(v___x_737_);
                        v___x_739_ = lean_string_append(v___x_736_, v___x_738_);
                        leanh::lean_dec_ref(v___x_738_);
                        v___x_740_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_740_, 0, v___x_739_);
                        v___x_741_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_741_, 0, v___x_718_);
                        leanh::lean_ctor_set(v___x_741_, 1, v___x_740_);
                        v___x_742_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_709_, v___x_741_, v_tail_713_);
                        return v___x_742_;
                    }
                } else {
                    if v___x_727_ == 0 {
                        v_a_743_ = lean_nat_abs(v_head_712_);
                        leanh::lean_dec(v_head_712_);
                        v___x_744_ = l_Nat_reprFast(v_a_743_);
                        v___y_721_ = v___x_744_;
                        state = 3;
                        continue;
                    } else {
                        v_abs_745_ = lean_nat_abs(v_head_712_);
                        leanh::lean_dec(v_head_712_);
                        v_one_746_ = leanh::lean_unsigned_to_nat(1);
                        v_a_747_ = lean_nat_sub(v_abs_745_, v_one_746_);
                        leanh::lean_dec(v_abs_745_);
                        v___x_748_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_749_ = lean_nat_add(v_a_747_, v_one_746_);
                        leanh::lean_dec(v_a_747_);
                        v___x_750_ = l_Nat_reprFast(v___x_749_);
                        v___x_751_ = lean_string_append(v___x_748_, v___x_750_);
                        leanh::lean_dec_ref(v___x_750_);
                        v___y_721_ = v___x_751_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_722_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_722_, 0, v___y_721_);
                v___x_723_ = l_Repr_addAppParen(v___x_722_, v___x_719_);
                v___x_724_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_724_, 0, v___x_718_);
                leanh::lean_ctor_set(v___x_724_, 1, v___x_723_);
                v___x_725_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2_spec__3(v_x_709_, v___x_724_, v_tail_713_);
                return v___x_725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(
    mut v___y_754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u8 = 0;
    let mut v_a_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_755_ = leanh::lean_unsigned_to_nat(0);
                v___x_760_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v___x_761_ = lean_int_dec_lt(v___y_754_, v___x_760_);
                if v___x_761_ == 0 {
                    if v___x_761_ == 0 {
                        v_a_762_ = lean_nat_abs(v___y_754_);
                        v___x_763_ = l_Nat_reprFast(v_a_762_);
                        v___x_764_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_764_, 0, v___x_763_);
                        return v___x_764_;
                    } else {
                        v_abs_765_ = lean_nat_abs(v___y_754_);
                        v_one_766_ = leanh::lean_unsigned_to_nat(1);
                        v_a_767_ = lean_nat_sub(v_abs_765_, v_one_766_);
                        leanh::lean_dec(v_abs_765_);
                        v___x_768_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_769_ = lean_nat_add(v_a_767_, v_one_766_);
                        leanh::lean_dec(v_a_767_);
                        v___x_770_ = l_Nat_reprFast(v___x_769_);
                        v___x_771_ = lean_string_append(v___x_768_, v___x_770_);
                        leanh::lean_dec_ref(v___x_770_);
                        v___x_772_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_772_, 0, v___x_771_);
                        return v___x_772_;
                    }
                } else {
                    if v___x_761_ == 0 {
                        v_a_773_ = lean_nat_abs(v___y_754_);
                        v___x_774_ = l_Nat_reprFast(v_a_773_);
                        v___y_757_ = v___x_774_;
                        state = 1;
                        continue;
                    } else {
                        v_abs_775_ = lean_nat_abs(v___y_754_);
                        v_one_776_ = leanh::lean_unsigned_to_nat(1);
                        v_a_777_ = lean_nat_sub(v_abs_775_, v_one_776_);
                        leanh::lean_dec(v_abs_775_);
                        v___x_778_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_779_ = lean_nat_add(v_a_777_, v_one_776_);
                        leanh::lean_dec(v_a_777_);
                        v___x_780_ = l_Nat_reprFast(v___x_779_);
                        v___x_781_ = lean_string_append(v___x_778_, v___x_780_);
                        leanh::lean_dec_ref(v___x_780_);
                        v___y_757_ = v___x_781_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_758_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_758_, 0, v___y_757_);
                v___x_759_ = l_Repr_addAppParen(v___x_758_, v___x_755_);
                return v___x_759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0___boxed(
    mut v___y_782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_783_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v___y_782_);
    leanh::lean_dec(v___y_782_);
    return v_res_783_;
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0(
    mut v_x_784_: *mut leanh::LeanObject,
    mut v_x_785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_784_) == 0 {
        let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_785_);
        v___x_786_ = leanh::lean_box(0);
        return v___x_786_;
    } else {
        let mut v_tail_787_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_787_ = leanh::lean_ctor_get(v_x_784_, 1);
        if leanh::lean_obj_tag(v_tail_787_) == 0 {
            let mut v_head_788_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_785_);
            v_head_788_ = leanh::lean_ctor_get(v_x_784_, 0);
            leanh::lean_inc(v_head_788_);
            leanh::lean_dec_ref_known(v_x_784_, 2);
            v___x_789_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v_head_788_);
            leanh::lean_dec(v_head_788_);
            return v___x_789_;
        } else {
            let mut v_head_790_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_787_);
            v_head_790_ = leanh::lean_ctor_get(v_x_784_, 0);
            leanh::lean_inc(v_head_790_);
            leanh::lean_dec_ref_known(v_x_784_, 2);
            v___x_791_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0___lam__0(v_head_790_);
            leanh::lean_dec(v_head_790_);
            v___x_792_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0_spec__2(v_x_785_, v___x_791_, v_tail_787_);
            return v___x_792_;
        }
    }
}
pub unsafe fn _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ =
        l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__2;
    v___x_805_ = lean_string_length(v___x_804_);
    return v___x_805_;
}
pub unsafe fn _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_806_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7_once), _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__7);
    v___x_807_ = lean_nat_to_int(v___x_806_);
    return v___x_807_;
}
pub unsafe fn l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(
    mut v_a_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_812_) == 0 {
        let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_813_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__1;
        return v___x_813_;
    } else {
        let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_814_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__5;
        v___x_815_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0_spec__0(v_a_812_, v___x_814_);
        v___x_816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8_once), _init_l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__8);
        v___x_817_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__9;
        v___x_818_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_818_, 0, v___x_817_);
        leanh::lean_ctor_set(v___x_818_, 1, v___x_815_);
        v___x_819_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__10;
        v___x_820_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_820_, 0, v___x_818_);
        leanh::lean_ctor_set(v___x_820_, 1, v___x_819_);
        v___x_821_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_821_, 0, v___x_816_);
        leanh::lean_ctor_set(v___x_821_, 1, v___x_820_);
        v___x_822_ = l_Std_Format_fill(v___x_821_);
        return v___x_822_;
    }
}
pub unsafe fn _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = leanh::lean_unsigned_to_nat(9);
    v___x_837_ = lean_nat_to_int(v___x_836_);
    return v___x_837_;
}
pub unsafe fn _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_841_ = leanh::lean_unsigned_to_nat(10);
    v___x_842_ = lean_nat_to_int(v___x_841_);
    return v___x_842_;
}
pub unsafe fn _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ = l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__0;
    v___x_845_ = lean_string_length(v___x_844_);
    return v___x_845_;
}
pub unsafe fn _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12_once),
        _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__12,
    );
    v___x_847_ = lean_nat_to_int(v___x_846_);
    return v___x_847_;
}
pub unsafe fn l_Lean_Omega_instReprLinearCombo_repr___redArg(
    mut v_x_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_const_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_857_: u8 = 0;
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: u8 = 0;
    let mut v_a_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_915_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_const_853_ = leanh::lean_ctor_get(v_x_852_, 0);
                v_coeffs_854_ = leanh::lean_ctor_get(v_x_852_, 1);
                v_isSharedCheck_915_ = (!leanh::lean_is_exclusive(v_x_852_)) as u8;
                if v_isSharedCheck_915_ == 0 {
                    v___x_856_ = v_x_852_;
                    v_isShared_857_ = v_isSharedCheck_915_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_coeffs_854_);
                    leanh::lean_inc(v_const_853_);
                    leanh::lean_dec(v_x_852_);
                    v___x_856_ = leanh::lean_box(0);
                    v_isShared_857_ = v_isSharedCheck_915_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_858_ = l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__5;
                v___x_859_ = l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__6;
                v___x_860_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__7,
                );
                v___x_888_ = leanh::lean_unsigned_to_nat(0);
                v___x_893_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v___x_894_ = lean_int_dec_lt(v_const_853_, v___x_893_);
                if v___x_894_ == 0 {
                    if v___x_894_ == 0 {
                        v_a_895_ = lean_nat_abs(v_const_853_);
                        leanh::lean_dec(v_const_853_);
                        v___x_896_ = l_Nat_reprFast(v_a_895_);
                        v___x_897_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_897_, 0, v___x_896_);
                        v___y_862_ = v___x_897_;
                        state = 2;
                        continue;
                    } else {
                        v_abs_898_ = lean_nat_abs(v_const_853_);
                        leanh::lean_dec(v_const_853_);
                        v_one_899_ = leanh::lean_unsigned_to_nat(1);
                        v_a_900_ = lean_nat_sub(v_abs_898_, v_one_899_);
                        leanh::lean_dec(v_abs_898_);
                        v___x_901_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_902_ = lean_nat_add(v_a_900_, v_one_899_);
                        leanh::lean_dec(v_a_900_);
                        v___x_903_ = l_Nat_reprFast(v___x_902_);
                        v___x_904_ = lean_string_append(v___x_901_, v___x_903_);
                        leanh::lean_dec_ref(v___x_903_);
                        v___x_905_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_905_, 0, v___x_904_);
                        v___y_862_ = v___x_905_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v___x_894_ == 0 {
                        v_a_906_ = lean_nat_abs(v_const_853_);
                        leanh::lean_dec(v_const_853_);
                        v___x_907_ = l_Nat_reprFast(v_a_906_);
                        v___y_890_ = v___x_907_;
                        state = 4;
                        continue;
                    } else {
                        v_abs_908_ = lean_nat_abs(v_const_853_);
                        leanh::lean_dec(v_const_853_);
                        v_one_909_ = leanh::lean_unsigned_to_nat(1);
                        v_a_910_ = lean_nat_sub(v_abs_908_, v_one_909_);
                        leanh::lean_dec(v_abs_908_);
                        v___x_911_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                        v___x_912_ = lean_nat_add(v_a_910_, v_one_909_);
                        leanh::lean_dec(v_a_910_);
                        v___x_913_ = l_Nat_reprFast(v___x_912_);
                        v___x_914_ = lean_string_append(v___x_911_, v___x_913_);
                        leanh::lean_dec_ref(v___x_913_);
                        v___y_890_ = v___x_914_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_857_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_856_, 4);
                    leanh::lean_ctor_set(v___x_856_, 1, v___y_862_);
                    leanh::lean_ctor_set(v___x_856_, 0, v___x_860_);
                    v___x_864_ = v___x_856_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_887_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_887_, 1, v___y_862_);
                    v___x_864_ = v_reuseFailAlloc_887_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_865_ = 0;
                v___x_866_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_866_, 0, v___x_864_);
                leanh::lean_ctor_set_uint8(
                    v___x_866_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_865_,
                );
                v___x_867_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_867_, 0, v___x_859_);
                leanh::lean_ctor_set(v___x_867_, 1, v___x_866_);
                v___x_868_ = l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg___closed__4;
                v___x_869_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_869_, 0, v___x_867_);
                leanh::lean_ctor_set(v___x_869_, 1, v___x_868_);
                v___x_870_ = leanh::lean_box(1);
                v___x_871_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_871_, 0, v___x_869_);
                leanh::lean_ctor_set(v___x_871_, 1, v___x_870_);
                v___x_872_ = l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__9;
                v___x_873_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_873_, 0, v___x_871_);
                leanh::lean_ctor_set(v___x_873_, 1, v___x_872_);
                v___x_874_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_874_, 0, v___x_873_);
                leanh::lean_ctor_set(v___x_874_, 1, v___x_858_);
                v___x_875_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10_once
                    ),
                    _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__10,
                );
                v___x_876_ =
                    l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(
                        v_coeffs_854_,
                    );
                v___x_877_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_877_, 0, v___x_875_);
                leanh::lean_ctor_set(v___x_877_, 1, v___x_876_);
                v___x_878_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_878_, 0, v___x_877_);
                leanh::lean_ctor_set_uint8(
                    v___x_878_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_865_,
                );
                v___x_879_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_879_, 0, v___x_874_);
                leanh::lean_ctor_set(v___x_879_, 1, v___x_878_);
                v___x_880_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13_once
                    ),
                    _init_l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__13,
                );
                v___x_881_ = l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__14;
                v___x_882_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_882_, 0, v___x_881_);
                leanh::lean_ctor_set(v___x_882_, 1, v___x_879_);
                v___x_883_ = l_Lean_Omega_instReprLinearCombo_repr___redArg___closed__15;
                v___x_884_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_884_, 0, v___x_882_);
                leanh::lean_ctor_set(v___x_884_, 1, v___x_883_);
                v___x_885_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_885_, 0, v___x_880_);
                leanh::lean_ctor_set(v___x_885_, 1, v___x_884_);
                v___x_886_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_886_, 0, v___x_885_);
                leanh::lean_ctor_set_uint8(
                    v___x_886_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_865_,
                );
                return v___x_886_;
            }
            4 => {
                v___x_891_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_891_, 0, v___y_890_);
                v___x_892_ = l_Repr_addAppParen(v___x_891_, v___x_888_);
                v___y_862_ = v___x_892_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_instReprLinearCombo_repr(
    mut v_x_916_: *mut leanh::LeanObject,
    mut v_prec_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = l_Lean_Omega_instReprLinearCombo_repr___redArg(v_x_916_);
    return v___x_918_;
}
pub unsafe fn l_Lean_Omega_instReprLinearCombo_repr___boxed(
    mut v_x_919_: *mut leanh::LeanObject,
    mut v_prec_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ = l_Lean_Omega_instReprLinearCombo_repr(v_x_919_, v_prec_920_);
    leanh::lean_dec(v_prec_920_);
    return v_res_921_;
}
pub unsafe fn l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0(
    mut v_a_922_: *mut leanh::LeanObject,
    mut v_n_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ =
        l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___redArg(v_a_922_);
    return v___x_924_;
}
pub unsafe fn l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0___boxed(
    mut v_a_925_: *mut leanh::LeanObject,
    mut v_n_926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_927_ =
        l_List_repr_x27___at___00Lean_Omega_instReprLinearCombo_repr_spec__0(v_a_925_, v_n_926_);
    leanh::lean_dec(v_n_926_);
    return v_res_927_;
}
pub unsafe fn l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(
    mut v_x_930_: *mut leanh::LeanObject,
    mut v_x_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_931_) == 0 {
                    return v_x_930_;
                } else {
                    v_head_932_ = leanh::lean_ctor_get(v_x_931_, 0);
                    v_tail_933_ = leanh::lean_ctor_get(v_x_931_, 1);
                    v___x_934_ = lean_string_append(v_x_930_, v_head_932_);
                    v_x_930_ = v___x_934_;
                    v_x_931_ = v_tail_933_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0___boxed(
    mut v_x_936_: *mut leanh::LeanObject,
    mut v_x_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(v_x_936_, v_x_937_);
    leanh::lean_dec(v_x_937_);
    return v_res_938_;
}
pub unsafe fn l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(
    mut v_l_940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___closed__0;
    v___x_942_ = l_List_foldl___at___00__private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join_spec__0(v___x_941_, v_l_940_);
    return v___x_942_;
}
pub unsafe fn l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join___boxed(
    mut v_l_943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_944_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v_l_943_);
    leanh::lean_dec(v_l_943_);
    return v_res_944_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_instToString___private__1___lam__0(
    mut v_x_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_961_: u8 = 0;
    let mut v_a_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_948_ = leanh::lean_ctor_get(v_x_947_, 0);
                v_snd_949_ = leanh::lean_ctor_get(v_x_947_, 1);
                v___x_950_ =
                    l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__0;
                v_intZero_960_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v_isNeg_961_ = lean_int_dec_lt(v_fst_948_, v_intZero_960_);
                if v_isNeg_961_ == 0 {
                    v_a_962_ = lean_nat_abs(v_fst_948_);
                    v___x_963_ = l_Nat_reprFast(v_a_962_);
                    v___y_952_ = v___x_963_;
                    state = 1;
                    continue;
                } else {
                    v_abs_964_ = lean_nat_abs(v_fst_948_);
                    v_one_965_ = leanh::lean_unsigned_to_nat(1);
                    v_a_966_ = lean_nat_sub(v_abs_964_, v_one_965_);
                    leanh::lean_dec(v_abs_964_);
                    v___x_967_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                    v___x_968_ = lean_nat_add(v_a_966_, v_one_965_);
                    leanh::lean_dec(v_a_966_);
                    v___x_969_ = l_Nat_reprFast(v___x_968_);
                    v___x_970_ = lean_string_append(v___x_967_, v___x_969_);
                    leanh::lean_dec_ref(v___x_969_);
                    v___y_952_ = v___x_970_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_953_ = lean_string_append(v___x_950_, v___y_952_);
                leanh::lean_dec_ref(v___y_952_);
                v___x_954_ =
                    l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___closed__1;
                v___x_955_ = lean_string_append(v___x_953_, v___x_954_);
                v___x_956_ = leanh::lean_unsigned_to_nat(1);
                v___x_957_ = lean_nat_add(v_snd_949_, v___x_956_);
                v___x_958_ = l_Nat_reprFast(v___x_957_);
                v___x_959_ = lean_string_append(v___x_955_, v___x_958_);
                leanh::lean_dec_ref(v___x_958_);
                return v___x_959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_LinearCombo_instToString___private__1___lam__0___boxed(
    mut v_x_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_972_ = l_Lean_Omega_LinearCombo_instToString___private__1___lam__0(v_x_971_);
    leanh::lean_dec_ref(v_x_971_);
    return v_res_972_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_instToString___private__1(
    mut v_lc_974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_const_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_987_: u8 = 0;
    let mut v_a_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_const_975_ = leanh::lean_ctor_get(v_lc_974_, 0);
                leanh::lean_inc(v_const_975_);
                v_coeffs_976_ = leanh::lean_ctor_get(v_lc_974_, 1);
                leanh::lean_inc(v_coeffs_976_);
                leanh::lean_dec_ref(v_lc_974_);
                v___f_977_ = l_Lean_Omega_LinearCombo_instToString___private__1___closed__0;
                v_intZero_986_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v_isNeg_987_ = lean_int_dec_lt(v_const_975_, v_intZero_986_);
                if v_isNeg_987_ == 0 {
                    v_a_988_ = lean_nat_abs(v_const_975_);
                    leanh::lean_dec(v_const_975_);
                    v___x_989_ = l_Nat_reprFast(v_a_988_);
                    v___y_979_ = v___x_989_;
                    state = 1;
                    continue;
                } else {
                    v_abs_990_ = lean_nat_abs(v_const_975_);
                    leanh::lean_dec(v_const_975_);
                    v_one_991_ = leanh::lean_unsigned_to_nat(1);
                    v_a_992_ = lean_nat_sub(v_abs_990_, v_one_991_);
                    leanh::lean_dec(v_abs_990_);
                    v___x_993_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                    v___x_994_ = lean_nat_add(v_a_992_, v_one_991_);
                    leanh::lean_dec(v_a_992_);
                    v___x_995_ = l_Nat_reprFast(v___x_994_);
                    v___x_996_ = lean_string_append(v___x_993_, v___x_995_);
                    leanh::lean_dec_ref(v___x_995_);
                    v___y_979_ = v___x_996_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_980_ = leanh::lean_unsigned_to_nat(0);
                v___x_981_ = l_List_zipIdx___redArg(v_coeffs_976_, v___x_980_);
                v___x_982_ = leanh::lean_box(0);
                v___x_983_ = l_List_mapTR_loop___redArg(v___f_977_, v___x_981_, v___x_982_);
                v___x_984_ =
                    l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v___x_983_);
                leanh::lean_dec(v___x_983_);
                v___x_985_ = lean_string_append(v___y_979_, v___x_984_);
                leanh::lean_dec_ref(v___x_984_);
                return v___x_985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_LinearCombo_instToString___lam__1(
    mut v___f_997_: *mut leanh::LeanObject,
    mut v_lc_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_const_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1010_: u8 = 0;
    let mut v_a_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_const_999_ = leanh::lean_ctor_get(v_lc_998_, 0);
                leanh::lean_inc(v_const_999_);
                v_coeffs_1000_ = leanh::lean_ctor_get(v_lc_998_, 1);
                leanh::lean_inc(v_coeffs_1000_);
                leanh::lean_dec_ref(v_lc_998_);
                v_intZero_1009_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v_isNeg_1010_ = lean_int_dec_lt(v_const_999_, v_intZero_1009_);
                if v_isNeg_1010_ == 0 {
                    v_a_1011_ = lean_nat_abs(v_const_999_);
                    leanh::lean_dec(v_const_999_);
                    v___x_1012_ = l_Nat_reprFast(v_a_1011_);
                    v___y_1002_ = v___x_1012_;
                    state = 1;
                    continue;
                } else {
                    v_abs_1013_ = lean_nat_abs(v_const_999_);
                    leanh::lean_dec(v_const_999_);
                    v_one_1014_ = leanh::lean_unsigned_to_nat(1);
                    v_a_1015_ = lean_nat_sub(v_abs_1013_, v_one_1014_);
                    leanh::lean_dec(v_abs_1013_);
                    v___x_1016_ = l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__1;
                    v___x_1017_ = lean_nat_add(v_a_1015_, v_one_1014_);
                    leanh::lean_dec(v_a_1015_);
                    v___x_1018_ = l_Nat_reprFast(v___x_1017_);
                    v___x_1019_ = lean_string_append(v___x_1016_, v___x_1018_);
                    leanh::lean_dec_ref(v___x_1018_);
                    v___y_1002_ = v___x_1019_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1003_ = leanh::lean_unsigned_to_nat(0);
                v___x_1004_ = l_List_zipIdx___redArg(v_coeffs_1000_, v___x_1003_);
                v___x_1005_ = leanh::lean_box(0);
                v___x_1006_ = l_List_mapTR_loop___redArg(v___f_997_, v___x_1004_, v___x_1005_);
                v___x_1007_ =
                    l___private_Init_Omega_LinearCombo_0__Lean_Omega_LinearCombo_join(v___x_1006_);
                leanh::lean_dec(v___x_1006_);
                v___x_1008_ = lean_string_append(v___y_1002_, v___x_1007_);
                leanh::lean_dec_ref(v___x_1007_);
                return v___x_1008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = leanh::lean_unsigned_to_nat(1);
    v___x_1024_ = lean_nat_to_int(v___x_1023_);
    return v___x_1024_;
}
pub unsafe fn _init_l_Lean_Omega_LinearCombo_instInhabited___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1025_ = leanh::lean_box(0);
    v___x_1026_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_LinearCombo_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Omega_LinearCombo_instInhabited___closed__0_once),
        _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0,
    );
    v___x_1027_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    leanh::lean_ctor_set(v___x_1027_, 1, v___x_1025_);
    return v___x_1027_;
}
pub unsafe fn _init_l_Lean_Omega_LinearCombo_instInhabited() -> *mut leanh::LeanObject {
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1028_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_LinearCombo_instInhabited___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Omega_LinearCombo_instInhabited___closed__1_once),
        _init_l_Lean_Omega_LinearCombo_instInhabited___closed__1,
    );
    return v___x_1028_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__1(
    mut v_a_1029_: *mut leanh::LeanObject,
    mut v_a_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1036_: u8 = 0;
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: u8 = 0;
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1029_) == 0 {
                    v___x_1031_ = l_List_reverse___redArg(v_a_1030_);
                    return v___x_1031_;
                } else {
                    v_head_1032_ = leanh::lean_ctor_get(v_a_1029_, 0);
                    v_tail_1033_ = leanh::lean_ctor_get(v_a_1029_, 1);
                    v_isSharedCheck_1044_ = (!leanh::lean_is_exclusive(v_a_1029_)) as u8;
                    if v_isSharedCheck_1044_ == 0 {
                        v___x_1035_ = v_a_1029_;
                        v_isShared_1036_ = v_isSharedCheck_1044_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1033_);
                        leanh::lean_inc(v_head_1032_);
                        leanh::lean_dec(v_a_1029_);
                        v___x_1035_ = leanh::lean_box(0);
                        v_isShared_1036_ = v_isSharedCheck_1044_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1037_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_LinearCombo_instInhabited___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Omega_LinearCombo_instInhabited___closed__0_once
                    ),
                    _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0,
                );
                v___x_1038_ = lean_int_dec_eq(v_head_1032_, v___x_1037_);
                if v___x_1038_ == 0 {
                    leanh::lean_del_object(v___x_1035_);
                    leanh::lean_dec(v_head_1032_);
                    v_a_1029_ = v_tail_1033_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_1036_ == 0 {
                        leanh::lean_ctor_set(v___x_1035_, 1, v_a_1030_);
                        v___x_1041_ = v___x_1035_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1043_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_head_1032_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_a_1030_);
                        v___x_1041_ = v_reuseFailAlloc_1043_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_1029_ = v_tail_1033_;
                v_a_1030_ = v___x_1041_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__0(
    mut v_x_1045_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1046_: u8 = 0;
    let mut v_head_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1050_: u8 = 0;
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1045_) == 0 {
                    v___x_1046_ = 1;
                    return v___x_1046_;
                } else {
                    v_head_1047_ = leanh::lean_ctor_get(v_x_1045_, 0);
                    v_tail_1048_ = leanh::lean_ctor_get(v_x_1045_, 1);
                    v___x_1052_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                    v___x_1053_ = lean_int_dec_eq(v_head_1047_, v___x_1052_);
                    if v___x_1053_ == 0 {
                        v___x_1054_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Omega_LinearCombo_instInhabited___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Omega_LinearCombo_instInhabited___closed__0_once
                            ),
                            _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0,
                        );
                        v___x_1055_ = lean_int_dec_eq(v_head_1047_, v___x_1054_);
                        v___y_1050_ = v___x_1055_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1050_ = v___x_1053_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1050_ == 0 {
                    return v___y_1050_;
                } else {
                    v_x_1045_ = v_tail_1048_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__0___boxed(
    mut v_x_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1057_: u8 = 0;
    let mut v_r_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ = l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__0(v_x_1056_);
    leanh::lean_dec(v_x_1056_);
    v_r_1058_ = leanh::lean_box((v_res_1057_) as usize);
    return v_r_1058_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_isAtom(mut v_a_1059_: *mut leanh::LeanObject) -> u8 {
    let mut v_const_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1063_: u8 = 0;
    let mut v___x_1064_: u8 = 0;
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_const_1060_ = leanh::lean_ctor_get(v_a_1059_, 0);
                leanh::lean_inc(v_const_1060_);
                v_coeffs_1061_ = leanh::lean_ctor_get(v_a_1059_, 1);
                leanh::lean_inc(v_coeffs_1061_);
                leanh::lean_dec_ref(v_a_1059_);
                v___x_1065_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
                v___x_1066_ = lean_int_dec_eq(v_const_1060_, v___x_1065_);
                leanh::lean_dec(v_const_1060_);
                if v___x_1066_ == 0 {
                    v___y_1063_ = v___x_1066_;
                    state = 1;
                    continue;
                } else {
                    v___x_1067_ = leanh::lean_box(0);
                    leanh::lean_inc(v_coeffs_1061_);
                    v___x_1068_ =
                        l_List_filterTR_loop___at___00Lean_Omega_LinearCombo_isAtom_spec__1(
                            v_coeffs_1061_,
                            v___x_1067_,
                        );
                    v___x_1069_ = l_List_lengthTR___redArg(v___x_1068_);
                    leanh::lean_dec(v___x_1068_);
                    v___x_1070_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1071_ = lean_nat_dec_eq(v___x_1069_, v___x_1070_);
                    leanh::lean_dec(v___x_1069_);
                    v___y_1063_ = v___x_1071_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1063_ == 0 {
                    leanh::lean_dec(v_coeffs_1061_);
                    return v___y_1063_;
                } else {
                    v___x_1064_ =
                        l_List_all___at___00Lean_Omega_LinearCombo_isAtom_spec__0(v_coeffs_1061_);
                    leanh::lean_dec(v_coeffs_1061_);
                    return v___x_1064_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_LinearCombo_isAtom___boxed(
    mut v_a_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1073_: u8 = 0;
    let mut v_r_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1073_ = l_Lean_Omega_LinearCombo_isAtom(v_a_1072_);
    v_r_1074_ = leanh::lean_box((v_res_1073_) as usize);
    return v_r_1074_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_eval(
    mut v_lc_1075_: *mut leanh::LeanObject,
    mut v_values_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_const_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_const_1077_ = leanh::lean_ctor_get(v_lc_1075_, 0);
    v_coeffs_1078_ = leanh::lean_ctor_get(v_lc_1075_, 1);
    v___x_1079_ = l_Lean_Omega_IntList_dot(v_coeffs_1078_, v_values_1076_);
    v___x_1080_ = lean_int_add(v_const_1077_, v___x_1079_);
    leanh::lean_dec(v___x_1079_);
    return v___x_1080_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_eval___boxed(
    mut v_lc_1081_: *mut leanh::LeanObject,
    mut v_values_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ = l_Lean_Omega_LinearCombo_eval(v_lc_1081_, v_values_1082_);
    leanh::lean_dec_ref(v_lc_1081_);
    return v_res_1083_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_coordinate(
    mut v_i_1084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0_once), _init_l___private_Init_Omega_LinearCombo_0__Lean_Omega_instToStringInt___lam__0___closed__0);
    v___x_1086_ = leanh::lean_box(0);
    v___x_1087_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_LinearCombo_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Omega_LinearCombo_instInhabited___closed__0_once),
        _init_l_Lean_Omega_LinearCombo_instInhabited___closed__0,
    );
    v___x_1088_ = l_Lean_Omega_IntList_set(v___x_1086_, v_i_1084_, v___x_1087_);
    v___x_1089_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1089_, 0, v___x_1085_);
    leanh::lean_ctor_set(v___x_1089_, 1, v___x_1088_);
    return v___x_1089_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_coordinate___boxed(
    mut v_i_1090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1091_ = l_Lean_Omega_LinearCombo_coordinate(v_i_1090_);
    leanh::lean_dec(v_i_1090_);
    return v_res_1091_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_add(
    mut v_l_u2081_1092_: *mut leanh::LeanObject,
    mut v_l_u2082_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_const_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_const_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1100_: u8 = 0;
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_const_1094_ = leanh::lean_ctor_get(v_l_u2081_1092_, 0);
                leanh::lean_inc(v_const_1094_);
                v_coeffs_1095_ = leanh::lean_ctor_get(v_l_u2081_1092_, 1);
                leanh::lean_inc(v_coeffs_1095_);
                leanh::lean_dec_ref(v_l_u2081_1092_);
                v_const_1096_ = leanh::lean_ctor_get(v_l_u2082_1093_, 0);
                v_coeffs_1097_ = leanh::lean_ctor_get(v_l_u2082_1093_, 1);
                v_isSharedCheck_1106_ = (!leanh::lean_is_exclusive(v_l_u2082_1093_)) as u8;
                if v_isSharedCheck_1106_ == 0 {
                    v___x_1099_ = v_l_u2082_1093_;
                    v_isShared_1100_ = v_isSharedCheck_1106_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_coeffs_1097_);
                    leanh::lean_inc(v_const_1096_);
                    leanh::lean_dec(v_l_u2082_1093_);
                    v___x_1099_ = leanh::lean_box(0);
                    v_isShared_1100_ = v_isSharedCheck_1106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1101_ = lean_int_add(v_const_1094_, v_const_1096_);
                leanh::lean_dec(v_const_1096_);
                leanh::lean_dec(v_const_1094_);
                v___x_1102_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(
                    v_coeffs_1095_,
                    v_coeffs_1097_,
                );
                if v_isShared_1100_ == 0 {
                    leanh::lean_ctor_set(v___x_1099_, 1, v___x_1102_);
                    leanh::lean_ctor_set(v___x_1099_, 0, v___x_1101_);
                    v___x_1104_ = v___x_1099_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1101_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1102_);
                    v___x_1104_ = v_reuseFailAlloc_1105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_LinearCombo_sub(
    mut v_l_u2081_1109_: *mut leanh::LeanObject,
    mut v_l_u2082_1110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_const_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_const_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_const_1111_ = leanh::lean_ctor_get(v_l_u2081_1109_, 0);
                leanh::lean_inc(v_const_1111_);
                v_coeffs_1112_ = leanh::lean_ctor_get(v_l_u2081_1109_, 1);
                leanh::lean_inc(v_coeffs_1112_);
                leanh::lean_dec_ref(v_l_u2081_1109_);
                v_const_1113_ = leanh::lean_ctor_get(v_l_u2082_1110_, 0);
                v_coeffs_1114_ = leanh::lean_ctor_get(v_l_u2082_1110_, 1);
                v_isSharedCheck_1123_ = (!leanh::lean_is_exclusive(v_l_u2082_1110_)) as u8;
                if v_isSharedCheck_1123_ == 0 {
                    v___x_1116_ = v_l_u2082_1110_;
                    v_isShared_1117_ = v_isSharedCheck_1123_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_coeffs_1114_);
                    leanh::lean_inc(v_const_1113_);
                    leanh::lean_dec(v_l_u2082_1110_);
                    v___x_1116_ = leanh::lean_box(0);
                    v_isShared_1117_ = v_isSharedCheck_1123_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1118_ = lean_int_sub(v_const_1111_, v_const_1113_);
                leanh::lean_dec(v_const_1113_);
                leanh::lean_dec(v_const_1111_);
                v___x_1119_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(
                    v_coeffs_1112_,
                    v_coeffs_1114_,
                );
                if v_isShared_1117_ == 0 {
                    leanh::lean_ctor_set(v___x_1116_, 1, v___x_1119_);
                    leanh::lean_ctor_set(v___x_1116_, 0, v___x_1118_);
                    v___x_1121_ = v___x_1116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1122_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1122_, 1, v___x_1119_);
                    v___x_1121_ = v_reuseFailAlloc_1122_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_LinearCombo_neg(
    mut v_lc_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_const_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1131_: u8 = 0;
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_const_1127_ = leanh::lean_ctor_get(v_lc_1126_, 0);
                v_coeffs_1128_ = leanh::lean_ctor_get(v_lc_1126_, 1);
                v_isSharedCheck_1137_ = (!leanh::lean_is_exclusive(v_lc_1126_)) as u8;
                if v_isSharedCheck_1137_ == 0 {
                    v___x_1130_ = v_lc_1126_;
                    v_isShared_1131_ = v_isSharedCheck_1137_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_coeffs_1128_);
                    leanh::lean_inc(v_const_1127_);
                    leanh::lean_dec(v_lc_1126_);
                    v___x_1130_ = leanh::lean_box(0);
                    v_isShared_1131_ = v_isSharedCheck_1137_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1132_ = lean_int_neg(v_const_1127_);
                leanh::lean_dec(v_const_1127_);
                v___x_1133_ = l_Lean_Omega_IntList_neg(v_coeffs_1128_);
                if v_isShared_1131_ == 0 {
                    leanh::lean_ctor_set(v___x_1130_, 1, v___x_1133_);
                    leanh::lean_ctor_set(v___x_1130_, 0, v___x_1132_);
                    v___x_1135_ = v___x_1130_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1136_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1132_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1133_);
                    v___x_1135_ = v_reuseFailAlloc_1136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_LinearCombo_smul(
    mut v_lc_1140_: *mut leanh::LeanObject,
    mut v_i_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_const_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_coeffs_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1146_: u8 = 0;
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_const_1142_ = leanh::lean_ctor_get(v_lc_1140_, 0);
                v_coeffs_1143_ = leanh::lean_ctor_get(v_lc_1140_, 1);
                v_isSharedCheck_1152_ = (!leanh::lean_is_exclusive(v_lc_1140_)) as u8;
                if v_isSharedCheck_1152_ == 0 {
                    v___x_1145_ = v_lc_1140_;
                    v_isShared_1146_ = v_isSharedCheck_1152_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_coeffs_1143_);
                    leanh::lean_inc(v_const_1142_);
                    leanh::lean_dec(v_lc_1140_);
                    v___x_1145_ = leanh::lean_box(0);
                    v_isShared_1146_ = v_isSharedCheck_1152_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1147_ = lean_int_mul(v_i_1141_, v_const_1142_);
                leanh::lean_dec(v_const_1142_);
                v___x_1148_ = l_Lean_Omega_IntList_smul(v_coeffs_1143_, v_i_1141_);
                if v_isShared_1146_ == 0 {
                    leanh::lean_ctor_set(v___x_1145_, 1, v___x_1148_);
                    leanh::lean_ctor_set(v___x_1145_, 0, v___x_1147_);
                    v___x_1150_ = v___x_1145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1151_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
                    v___x_1150_ = v_reuseFailAlloc_1151_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_LinearCombo_smul___boxed(
    mut v_lc_1153_: *mut leanh::LeanObject,
    mut v_i_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Lean_Omega_LinearCombo_smul(v_lc_1153_, v_i_1154_);
    leanh::lean_dec(v_i_1154_);
    return v_res_1155_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_instHMulInt___lam__0(
    mut v_i_1156_: *mut leanh::LeanObject,
    mut v_lc_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = l_Lean_Omega_LinearCombo_smul(v_lc_1157_, v_i_1156_);
    return v___x_1158_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_instHMulInt___lam__0___boxed(
    mut v_i_1159_: *mut leanh::LeanObject,
    mut v_lc_1160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1161_ = l_Lean_Omega_LinearCombo_instHMulInt___lam__0(v_i_1159_, v_lc_1160_);
    leanh::lean_dec(v_i_1159_);
    return v_res_1161_;
}
pub unsafe fn l_Lean_Omega_LinearCombo_mul(
    mut v_l_u2081_1164_: *mut leanh::LeanObject,
    mut v_l_u2082_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_const_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_const_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_const_1166_ = leanh::lean_ctor_get(v_l_u2082_1165_, 0);
    leanh::lean_inc(v_const_1166_);
    v_const_1167_ = leanh::lean_ctor_get(v_l_u2081_1164_, 0);
    leanh::lean_inc(v_const_1167_);
    v___x_1168_ = l_Lean_Omega_LinearCombo_smul(v_l_u2081_1164_, v_const_1166_);
    v___x_1169_ = l_Lean_Omega_LinearCombo_smul(v_l_u2082_1165_, v_const_1167_);
    v___x_1170_ = l_Lean_Omega_LinearCombo_add(v___x_1168_, v___x_1169_);
    v___x_1171_ = lean_int_mul(v_const_1167_, v_const_1166_);
    leanh::lean_dec(v_const_1166_);
    leanh::lean_dec(v_const_1167_);
    v___x_1172_ = leanh::lean_box(0);
    v___x_1173_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1173_, 0, v___x_1171_);
    leanh::lean_ctor_set(v___x_1173_, 1, v___x_1172_);
    v___x_1174_ = l_Lean_Omega_LinearCombo_sub(v___x_1170_, v___x_1173_);
    return v___x_1174_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Omega_LinearCombo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Omega_Coeffs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Omega_LinearCombo_instInhabited = _init_l_Lean_Omega_LinearCombo_instInhabited();
    leanh::lean_mark_persistent(l_Lean_Omega_LinearCombo_instInhabited);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Omega_LinearCombo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Omega_LinearCombo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Omega_Coeffs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega_LinearCombo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Omega_LinearCombo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Omega_LinearCombo(builtin);
}
// Lean compiler output
// Module: Lean.Meta.Match.AltTelescopes
// Imports: Lean.Meta.Match.MatcherInfo Lean.Meta.Match.NamedPatterns Lean.Meta.MatchUtil Lean.Meta.AppBuilder Init.Data.Nat.Order Init.Data.Order.Lemmas
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_set,
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv,
    lean_expr_instantiate1, lean_find_expr, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_st_ref_get, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_eraseIdx___redArg;
use crate::r#gen::Init::Data::Nat::Order::{
    initialize_Init_Data_Nat_Order, runtime_initialize_Init_Data_Nat_Order,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_fvarId_x21, l_Lean_Expr_isFVar, l_Lean_Expr_replaceFVar,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkHEqRefl,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instantiateForall,
    l_Lean_Meta_whnfForall, l_Lean_Meta_withReplaceFVarId___boxed,
    l_Lean_Meta_withReplaceFVarId___redArg,
};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    initialize_Lean_Meta_Match_MatcherInfo, runtime_initialize_Lean_Meta_Match_MatcherInfo,
};
use crate::r#gen::Lean::Meta::Match::NamedPatterns::{
    initialize_Lean_Meta_Match_NamedPatterns, l_Lean_Meta_Match_isNamedPattern_x3f,
    l_Lean_Meta_Match_unfoldNamedPattern, runtime_initialize_Lean_Meta_Match_NamedPatterns,
};
use crate::r#gen::Lean::Meta::MatchUtil::{
    initialize_Lean_Meta_MatchUtil, l_Lean_Meta_matchEq_x3f, l_Lean_Meta_matchHEq_x3f,
    runtime_initialize_Lean_Meta_MatchUtil,
};
pub static l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 120, 112, 101, 99, 116, 105, 110, 103, 32, 0]};
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 44, 32, 98, 117, 116, 32, 102, 111, 117, 110, 100, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1_value: leanh::LeanStringObject<83> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 65, 108, 116, 84, 101, 108, 101, 115, 99, 111, 112, 101, 115, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 102, 111, 114, 97, 108, 108, 65, 108, 116, 86, 97, 114, 115, 84, 101, 108, 101, 115, 99, 111, 112, 101, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 65, 108, 116, 84, 101, 108, 101, 115, 99, 111, 112, 101, 115, 0]};
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 102, 111, 114, 97,
        108, 108, 65, 108, 116, 86, 97, 114, 115, 84, 101, 108, 101, 115, 99, 111, 112, 101, 0,
    ],
};
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1_value:
    leanh::LeanStringObject<48> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 97, 108, 116, 73, 110, 102, 111, 46, 110, 117, 109, 79, 118, 101, 114, 108, 97,
        112, 115, 32, 61, 32, 48, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3_value:
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
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__4_value:
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
    m_data: [85, 110, 105, 116, 0],
};
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__5_value:
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
    m_data: [117, 110, 105, 116, 0],
};
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        9833841078580172006 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__5_value)
            as *mut leanh::LeanObject,
        565778312915565143 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9_value:
    leanh::LeanArrayObject<1> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 109, 97, 116, 99, 104, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [32, 101, 113, 117, 97, 108, 105, 116, 105, 101, 115, 44, 32, 98, 117, 116, 32, 102, 111, 117, 110, 100, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0(
    mut v_h_984_: *mut leanh::LeanObject,
    mut v_e_985_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_986_ = l_Lean_Meta_Match_isNamedPattern_x3f(v_e_985_);
    if leanh::lean_obj_tag(v___x_986_) == 1 {
        let mut v_val_987_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_989_: u8 = 0;
        v_val_987_ = leanh::lean_ctor_get(v___x_986_, 0);
        leanh::lean_inc(v_val_987_);
        leanh::lean_dec_ref_known(v___x_986_, 1);
        v___x_988_ = l_Lean_Expr_appArg_x21(v_val_987_);
        leanh::lean_dec(v_val_987_);
        v___x_989_ = lean_expr_eqv(v___x_988_, v_h_984_);
        leanh::lean_dec_ref(v___x_988_);
        return v___x_989_;
    } else {
        let mut v___x_990_: u8 = 0;
        leanh::lean_dec(v___x_986_);
        v___x_990_ = 0;
        return v___x_990_;
    }
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0___boxed(
    mut v_h_991_: *mut leanh::LeanObject,
    mut v_e_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_993_: u8 = 0;
    let mut v_r_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0(v_h_991_, v_e_992_);
    leanh::lean_dec_ref(v_e_992_);
    leanh::lean_dec_ref(v_h_991_);
    v_r_994_ = leanh::lean_box((v_res_993_) as usize);
    return v_r_994_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(
    mut v_type_995_: *mut leanh::LeanObject,
    mut v_h_996_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_997_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_997_, 0, v_h_996_);
    v___x_998_ = lean_find_expr(v___f_997_, v_type_995_);
    leanh::lean_dec_ref(v___f_997_);
    if leanh::lean_obj_tag(v___x_998_) == 0 {
        let mut v___x_999_: u8 = 0;
        v___x_999_ = 0;
        return v___x_999_;
    } else {
        let mut v___x_1000_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_998_, 1);
        v___x_1000_ = 1;
        return v___x_1000_;
    }
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof___boxed(
    mut v_type_1001_: *mut leanh::LeanObject,
    mut v_h_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1003_: u8 = 0;
    let mut v_r_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1003_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v_type_1001_, v_h_1002_);
    leanh::lean_dec_ref(v_type_1001_);
    v_r_1004_ = leanh::lean_box((v_res_1003_) as usize);
    return v_r_1004_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(
    mut v_msg_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
    mut v___y_1009_: *mut leanh::LeanObject,
    mut v___y_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401__overap_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1012_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0;
    v___x_2401__overap_1013_ = lean_panic_fn_borrowed(v___f_1012_, v_msg_1006_);
    leanh::lean_inc(v___y_1010_);
    leanh::lean_inc_ref(v___y_1009_);
    leanh::lean_inc(v___y_1008_);
    leanh::lean_inc_ref(v___y_1007_);
    v___x_1014_ = leanh::lean_apply_5(
        v___x_2401__overap_1013_,
        v___y_1007_,
        v___y_1008_,
        v___y_1009_,
        v___y_1010_,
        leanh::lean_box(0),
    );
    return v___x_1014_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___boxed(
    mut v_msg_1015_: *mut leanh::LeanObject,
    mut v___y_1016_: *mut leanh::LeanObject,
    mut v___y_1017_: *mut leanh::LeanObject,
    mut v___y_1018_: *mut leanh::LeanObject,
    mut v___y_1019_: *mut leanh::LeanObject,
    mut v___y_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1021_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v_msg_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
    leanh::lean_dec(v___y_1019_);
    leanh::lean_dec_ref(v___y_1018_);
    leanh::lean_dec(v___y_1017_);
    leanh::lean_dec_ref(v___y_1016_);
    return v_res_1021_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(
    mut v_xs_1022_: *mut leanh::LeanObject,
    mut v_v_1023_: *mut leanh::LeanObject,
    mut v_i_1024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: u8 = 0;
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1025_ = lean_array_get_size(v_xs_1022_);
                v___x_1026_ = lean_nat_dec_lt(v_i_1024_, v___x_1025_);
                if v___x_1026_ == 0 {
                    leanh::lean_dec(v_i_1024_);
                    v___x_1027_ = leanh::lean_box(0);
                    return v___x_1027_;
                } else {
                    v___x_1028_ = lean_array_fget_borrowed(v_xs_1022_, v_i_1024_);
                    v___x_1029_ = lean_expr_eqv(v___x_1028_, v_v_1023_);
                    if v___x_1029_ == 0 {
                        v___x_1030_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1031_ = lean_nat_add(v_i_1024_, v___x_1030_);
                        leanh::lean_dec(v_i_1024_);
                        v_i_1024_ = v___x_1031_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1033_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1033_, 0, v_i_1024_);
                        return v___x_1033_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2___boxed(
    mut v_xs_1034_: *mut leanh::LeanObject,
    mut v_v_1035_: *mut leanh::LeanObject,
    mut v_i_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1037_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(v_xs_1034_, v_v_1035_, v_i_1036_);
    leanh::lean_dec_ref(v_v_1035_);
    leanh::lean_dec_ref(v_xs_1034_);
    return v_res_1037_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(
    mut v_xs_1038_: *mut leanh::LeanObject,
    mut v_v_1039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = leanh::lean_unsigned_to_nat(0);
    v___x_1041_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1_spec__2(v_xs_1038_, v_v_1039_, v___x_1040_);
    return v___x_1041_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1___boxed(
    mut v_xs_1042_: *mut leanh::LeanObject,
    mut v_v_1043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1044_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_xs_1042_, v_v_1043_);
    leanh::lean_dec_ref(v_v_1043_);
    leanh::lean_dec_ref(v_xs_1042_);
    return v_res_1044_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(
    mut v_xs_1045_: *mut leanh::LeanObject,
    mut v_v_1046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1047_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_xs_1045_, v_v_1046_);
                if leanh::lean_obj_tag(v___x_1047_) == 0 {
                    v___x_1048_ = leanh::lean_box(0);
                    return v___x_1048_;
                } else {
                    v_val_1049_ = leanh::lean_ctor_get(v___x_1047_, 0);
                    v_isSharedCheck_1056_ = (!leanh::lean_is_exclusive(v___x_1047_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1051_ = v___x_1047_;
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1049_);
                        leanh::lean_dec(v___x_1047_);
                        v___x_1051_ = leanh::lean_box(0);
                        v_isShared_1052_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1052_ == 0 {
                    v___x_1054_ = v___x_1051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1055_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_val_1049_);
                    v___x_1054_ = v_reuseFailAlloc_1055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2___boxed(
    mut v_xs_1057_: *mut leanh::LeanObject,
    mut v_v_1058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1059_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(v_xs_1057_, v_v_1058_);
    leanh::lean_dec_ref(v_v_1058_);
    leanh::lean_dec_ref(v_xs_1057_);
    return v_res_1059_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(
    mut v_msgData_1060_: *mut leanh::LeanObject,
    mut v___y_1061_: *mut leanh::LeanObject,
    mut v___y_1062_: *mut leanh::LeanObject,
    mut v___y_1063_: *mut leanh::LeanObject,
    mut v___y_1064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1066_ = lean_st_ref_get(v___y_1064_);
    v_env_1067_ = leanh::lean_ctor_get(v___x_1066_, 0);
    leanh::lean_inc_ref(v_env_1067_);
    leanh::lean_dec(v___x_1066_);
    v___x_1068_ = lean_st_ref_get(v___y_1062_);
    v_mctx_1069_ = leanh::lean_ctor_get(v___x_1068_, 0);
    leanh::lean_inc_ref(v_mctx_1069_);
    leanh::lean_dec(v___x_1068_);
    v_lctx_1070_ = leanh::lean_ctor_get(v___y_1061_, 2);
    v_options_1071_ = leanh::lean_ctor_get(v___y_1063_, 2);
    leanh::lean_inc_ref(v_options_1071_);
    leanh::lean_inc_ref(v_lctx_1070_);
    v___x_1072_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1072_, 0, v_env_1067_);
    leanh::lean_ctor_set(v___x_1072_, 1, v_mctx_1069_);
    leanh::lean_ctor_set(v___x_1072_, 2, v_lctx_1070_);
    leanh::lean_ctor_set(v___x_1072_, 3, v_options_1071_);
    v___x_1073_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1073_, 0, v___x_1072_);
    leanh::lean_ctor_set(v___x_1073_, 1, v_msgData_1060_);
    v___x_1074_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1074_, 0, v___x_1073_);
    return v___x_1074_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9___boxed(
    mut v_msgData_1075_: *mut leanh::LeanObject,
    mut v___y_1076_: *mut leanh::LeanObject,
    mut v___y_1077_: *mut leanh::LeanObject,
    mut v___y_1078_: *mut leanh::LeanObject,
    mut v___y_1079_: *mut leanh::LeanObject,
    mut v___y_1080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1081_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msgData_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
    leanh::lean_dec(v___y_1079_);
    leanh::lean_dec_ref(v___y_1078_);
    leanh::lean_dec(v___y_1077_);
    leanh::lean_dec_ref(v___y_1076_);
    return v_res_1081_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(
    mut v_msg_1082_: *mut leanh::LeanObject,
    mut v___y_1083_: *mut leanh::LeanObject,
    mut v___y_1084_: *mut leanh::LeanObject,
    mut v___y_1085_: *mut leanh::LeanObject,
    mut v___y_1086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1088_ = leanh::lean_ctor_get(v___y_1085_, 5);
                v___x_1089_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6_spec__9(v_msg_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
                v_a_1090_ = leanh::lean_ctor_get(v___x_1089_, 0);
                v_isSharedCheck_1098_ = (!leanh::lean_is_exclusive(v___x_1089_)) as u8;
                if v_isSharedCheck_1098_ == 0 {
                    v___x_1092_ = v___x_1089_;
                    v_isShared_1093_ = v_isSharedCheck_1098_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1090_);
                    leanh::lean_dec(v___x_1089_);
                    v___x_1092_ = leanh::lean_box(0);
                    v_isShared_1093_ = v_isSharedCheck_1098_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1088_);
                v___x_1094_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1094_, 0, v_ref_1088_);
                leanh::lean_ctor_set(v___x_1094_, 1, v_a_1090_);
                if v_isShared_1093_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1092_, 1);
                    leanh::lean_ctor_set(v___x_1092_, 0, v___x_1094_);
                    v___x_1096_ = v___x_1092_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
                    v___x_1096_ = v_reuseFailAlloc_1097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg___boxed(
    mut v_msg_1099_: *mut leanh::LeanObject,
    mut v___y_1100_: *mut leanh::LeanObject,
    mut v___y_1101_: *mut leanh::LeanObject,
    mut v___y_1102_: *mut leanh::LeanObject,
    mut v___y_1103_: *mut leanh::LeanObject,
    mut v___y_1104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1105_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
    leanh::lean_dec(v___y_1103_);
    leanh::lean_dec_ref(v___y_1102_);
    leanh::lean_dec(v___y_1101_);
    leanh::lean_dec_ref(v___y_1100_);
    return v_res_1105_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(
    mut v_k_1106_: *mut leanh::LeanObject,
    mut v_b_1107_: *mut leanh::LeanObject,
    mut v___y_1108_: *mut leanh::LeanObject,
    mut v___y_1109_: *mut leanh::LeanObject,
    mut v___y_1110_: *mut leanh::LeanObject,
    mut v___y_1111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1111_);
    leanh::lean_inc_ref(v___y_1110_);
    leanh::lean_inc(v___y_1109_);
    leanh::lean_inc_ref(v___y_1108_);
    v___x_1113_ = leanh::lean_apply_6(
        v_k_1106_,
        v_b_1107_,
        v___y_1108_,
        v___y_1109_,
        v___y_1110_,
        v___y_1111_,
        leanh::lean_box(0),
    );
    return v___x_1113_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed(
    mut v_k_1114_: *mut leanh::LeanObject,
    mut v_b_1115_: *mut leanh::LeanObject,
    mut v___y_1116_: *mut leanh::LeanObject,
    mut v___y_1117_: *mut leanh::LeanObject,
    mut v___y_1118_: *mut leanh::LeanObject,
    mut v___y_1119_: *mut leanh::LeanObject,
    mut v___y_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1121_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0(v_k_1114_, v_b_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
    leanh::lean_dec(v___y_1119_);
    leanh::lean_dec_ref(v___y_1118_);
    leanh::lean_dec(v___y_1117_);
    leanh::lean_dec_ref(v___y_1116_);
    return v_res_1121_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(
    mut v_name_1122_: *mut leanh::LeanObject,
    mut v_bi_1123_: u8,
    mut v_type_1124_: *mut leanh::LeanObject,
    mut v_k_1125_: *mut leanh::LeanObject,
    mut v_kind_1126_: u8,
    mut v___y_1127_: *mut leanh::LeanObject,
    mut v___y_1128_: *mut leanh::LeanObject,
    mut v___y_1129_: *mut leanh::LeanObject,
    mut v___y_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1137_: u8 = 0;
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1141_: u8 = 0;
    let mut v_a_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1145_: u8 = 0;
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1132_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_1132_, 0, v_k_1125_);
                v___x_1133_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_1122_,
                    v_bi_1123_,
                    v_type_1124_,
                    v___f_1132_,
                    v_kind_1126_,
                    v___y_1127_,
                    v___y_1128_,
                    v___y_1129_,
                    v___y_1130_,
                );
                if leanh::lean_obj_tag(v___x_1133_) == 0 {
                    v_a_1134_ = leanh::lean_ctor_get(v___x_1133_, 0);
                    v_isSharedCheck_1141_ = (!leanh::lean_is_exclusive(v___x_1133_)) as u8;
                    if v_isSharedCheck_1141_ == 0 {
                        v___x_1136_ = v___x_1133_;
                        v_isShared_1137_ = v_isSharedCheck_1141_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1134_);
                        leanh::lean_dec(v___x_1133_);
                        v___x_1136_ = leanh::lean_box(0);
                        v_isShared_1137_ = v_isSharedCheck_1141_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1142_ = leanh::lean_ctor_get(v___x_1133_, 0);
                    v_isSharedCheck_1149_ = (!leanh::lean_is_exclusive(v___x_1133_)) as u8;
                    if v_isSharedCheck_1149_ == 0 {
                        v___x_1144_ = v___x_1133_;
                        v_isShared_1145_ = v_isSharedCheck_1149_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1142_);
                        leanh::lean_dec(v___x_1133_);
                        v___x_1144_ = leanh::lean_box(0);
                        v_isShared_1145_ = v_isSharedCheck_1149_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1137_ == 0 {
                    v___x_1139_ = v___x_1136_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1140_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
                    v___x_1139_ = v_reuseFailAlloc_1140_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1139_;
            }
            3 => {
                if v_isShared_1145_ == 0 {
                    v___x_1147_ = v___x_1144_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
                    v___x_1147_ = v_reuseFailAlloc_1148_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg___boxed(
    mut v_name_1150_: *mut leanh::LeanObject,
    mut v_bi_1151_: *mut leanh::LeanObject,
    mut v_type_1152_: *mut leanh::LeanObject,
    mut v_k_1153_: *mut leanh::LeanObject,
    mut v_kind_1154_: *mut leanh::LeanObject,
    mut v___y_1155_: *mut leanh::LeanObject,
    mut v___y_1156_: *mut leanh::LeanObject,
    mut v___y_1157_: *mut leanh::LeanObject,
    mut v___y_1158_: *mut leanh::LeanObject,
    mut v___y_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_1160_: u8 = 0;
    let mut v_kind_boxed_1161_: u8 = 0;
    let mut v_res_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1160_ = (leanh::lean_unbox(v_bi_1151_) as u8);
    v_kind_boxed_1161_ = (leanh::lean_unbox(v_kind_1154_) as u8);
    v_res_1162_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_1150_, v_bi_boxed_1160_, v_type_1152_, v_k_1153_, v_kind_boxed_1161_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
    leanh::lean_dec(v___y_1158_);
    leanh::lean_dec_ref(v___y_1157_);
    leanh::lean_dec(v___y_1156_);
    leanh::lean_dec_ref(v___y_1155_);
    return v_res_1162_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(
    mut v_name_1163_: *mut leanh::LeanObject,
    mut v_type_1164_: *mut leanh::LeanObject,
    mut v_k_1165_: *mut leanh::LeanObject,
    mut v___y_1166_: *mut leanh::LeanObject,
    mut v___y_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
    mut v___y_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1171_: u8 = 0;
    let mut v___x_1172_: u8 = 0;
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1171_ = 0;
    v___x_1172_ = 0;
    v___x_1173_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_1163_, v___x_1171_, v_type_1164_, v_k_1165_, v___x_1172_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
    return v___x_1173_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg___boxed(
    mut v_name_1174_: *mut leanh::LeanObject,
    mut v_type_1175_: *mut leanh::LeanObject,
    mut v_k_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
    mut v___y_1179_: *mut leanh::LeanObject,
    mut v___y_1180_: *mut leanh::LeanObject,
    mut v___y_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_1174_, v_type_1175_, v_k_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
    leanh::lean_dec(v___y_1180_);
    leanh::lean_dec_ref(v___y_1179_);
    leanh::lean_dec(v___y_1178_);
    leanh::lean_dec_ref(v___y_1177_);
    return v_res_1182_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(
    mut v_fst_1183_: *mut leanh::LeanObject,
    mut v_snd_1184_: *mut leanh::LeanObject,
    mut v_sz_1185_: usize,
    mut v_i_1186_: usize,
    mut v_bs_1187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1188_: u8 = 0;
    let mut v_v_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: usize = 0;
    let mut v___x_1195_: usize = 0;
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1188_ = lean_usize_dec_lt(v_i_1186_, v_sz_1185_);
                if v___x_1188_ == 0 {
                    leanh::lean_dec_ref(v_snd_1184_);
                    return v_bs_1187_;
                } else {
                    v_v_1189_ = lean_array_uget(v_bs_1187_, v_i_1186_);
                    v___x_1190_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1191_ = lean_array_uset(v_bs_1187_, v_i_1186_, v___x_1190_);
                    v___x_1198_ = lean_expr_eqv(v_v_1189_, v_fst_1183_);
                    if v___x_1198_ == 0 {
                        v___y_1193_ = v_v_1189_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_v_1189_);
                        leanh::lean_inc_ref(v_snd_1184_);
                        v___y_1193_ = v_snd_1184_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1194_ = 1usize;
                v___x_1195_ = lean_usize_add(v_i_1186_, v___x_1194_);
                v___x_1196_ = lean_array_uset(v_bs_x27_1191_, v_i_1186_, v___y_1193_);
                v_i_1186_ = v___x_1195_;
                v_bs_1187_ = v___x_1196_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3___boxed(
    mut v_fst_1199_: *mut leanh::LeanObject,
    mut v_snd_1200_: *mut leanh::LeanObject,
    mut v_sz_1201_: *mut leanh::LeanObject,
    mut v_i_1202_: *mut leanh::LeanObject,
    mut v_bs_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1204_: usize = 0;
    let mut v_i_boxed_1205_: usize = 0;
    let mut v_res_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1204_ = leanh::lean_unbox_usize(v_sz_1201_);
    leanh::lean_dec(v_sz_1201_);
    v_i_boxed_1205_ = leanh::lean_unbox_usize(v_i_1202_);
    leanh::lean_dec(v_i_1202_);
    v_res_1206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_1199_, v_snd_1200_, v_sz_boxed_1204_, v_i_boxed_1205_, v_bs_1203_);
    leanh::lean_dec_ref(v_fst_1199_);
    return v_res_1206_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(
    mut v_a_1207_: *mut leanh::LeanObject,
    mut v_as_1208_: *mut leanh::LeanObject,
    mut v_i_1209_: usize,
    mut v_stop_1210_: usize,
) -> u8 {
    let mut v___x_1211_: u8 = 0;
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: u8 = 0;
    let mut v___x_1214_: usize = 0;
    let mut v___x_1215_: usize = 0;
    let mut v___x_1217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1211_ = lean_usize_dec_eq(v_i_1209_, v_stop_1210_);
                if v___x_1211_ == 0 {
                    v___x_1212_ = lean_array_uget_borrowed(v_as_1208_, v_i_1209_);
                    v___x_1213_ = lean_expr_eqv(v_a_1207_, v___x_1212_);
                    if v___x_1213_ == 0 {
                        v___x_1214_ = 1usize;
                        v___x_1215_ = lean_usize_add(v_i_1209_, v___x_1214_);
                        v_i_1209_ = v___x_1215_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1213_;
                    }
                } else {
                    v___x_1217_ = 0;
                    return v___x_1217_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0___boxed(
    mut v_a_1218_: *mut leanh::LeanObject,
    mut v_as_1219_: *mut leanh::LeanObject,
    mut v_i_1220_: *mut leanh::LeanObject,
    mut v_stop_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1222_: usize = 0;
    let mut v_stop_boxed_1223_: usize = 0;
    let mut v_res_1224_: u8 = 0;
    let mut v_r_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1222_ = leanh::lean_unbox_usize(v_i_1220_);
    leanh::lean_dec(v_i_1220_);
    v_stop_boxed_1223_ = leanh::lean_unbox_usize(v_stop_1221_);
    leanh::lean_dec(v_stop_1221_);
    v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_1218_, v_as_1219_, v_i_boxed_1222_, v_stop_boxed_1223_);
    leanh::lean_dec_ref(v_as_1219_);
    leanh::lean_dec_ref(v_a_1218_);
    v_r_1225_ = leanh::lean_box((v_res_1224_) as usize);
    return v_r_1225_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(
    mut v_as_1226_: *mut leanh::LeanObject,
    mut v_a_1227_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u8 = 0;
    v___x_1228_ = leanh::lean_unsigned_to_nat(0);
    v___x_1229_ = lean_array_get_size(v_as_1226_);
    v___x_1230_ = lean_nat_dec_lt(v___x_1228_, v___x_1229_);
    if v___x_1230_ == 0 {
        return v___x_1230_;
    } else {
        if v___x_1230_ == 0 {
            return v___x_1230_;
        } else {
            let mut v___x_1231_: usize = 0;
            let mut v___x_1232_: usize = 0;
            let mut v___x_1233_: u8 = 0;
            v___x_1231_ = 0usize;
            v___x_1232_ = lean_usize_of_nat(v___x_1229_);
            v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0_spec__0(v_a_1227_, v_as_1226_, v___x_1231_, v___x_1232_);
            return v___x_1233_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0___boxed(
    mut v_as_1234_: *mut leanh::LeanObject,
    mut v_a_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1236_: u8 = 0;
    let mut v_r_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1236_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_as_1234_, v_a_1235_);
    leanh::lean_dec_ref(v_a_1235_);
    leanh::lean_dec_ref(v_as_1234_);
    v_r_1237_ = leanh::lean_box((v_res_1236_) as usize);
    return v_r_1237_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1239_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__0;
    v___x_1240_ = l_Lean_stringToMessageData(v___x_1239_);
    return v___x_1240_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1242_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__2;
    v___x_1243_ = l_Lean_stringToMessageData(v___x_1242_);
    return v___x_1243_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed(
    mut v_altType_1244_: *mut leanh::LeanObject,
    mut v_altInfo_1245_: *mut leanh::LeanObject,
    mut v_k_1246_: *mut leanh::LeanObject,
    mut v_ys_1247_: *mut leanh::LeanObject,
    mut v_args_1248_: *mut leanh::LeanObject,
    mut v_mask_1249_: *mut leanh::LeanObject,
    mut v_i_1250_: *mut leanh::LeanObject,
    mut v_type_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
    mut v_a_1253_: *mut leanh::LeanObject,
    mut v_a_1254_: *mut leanh::LeanObject,
    mut v_a_1255_: *mut leanh::LeanObject,
    mut v_a_1256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1257_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_1244_, v_altInfo_1245_, v_k_1246_, v_ys_1247_, v_args_1248_, v_mask_1249_, v_i_1250_, v_type_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
    leanh::lean_dec(v_a_1255_);
    leanh::lean_dec_ref(v_a_1254_);
    leanh::lean_dec(v_a_1253_);
    leanh::lean_dec_ref(v_a_1252_);
    return v_res_1257_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2;
    v___x_1262_ = leanh::lean_unsigned_to_nat(47);
    v___x_1263_ = leanh::lean_unsigned_to_nat(68);
    v___x_1264_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1;
    v___x_1265_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0;
    v___x_1266_ = l_mkPanicMessageWithDecl(
        v___x_1265_,
        v___x_1264_,
        v___x_1263_,
        v___x_1262_,
        v___x_1261_,
    );
    return v___x_1266_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1267_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__2;
    v___x_1268_ = leanh::lean_unsigned_to_nat(48);
    v___x_1269_ = leanh::lean_unsigned_to_nat(66);
    v___x_1270_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__1;
    v___x_1271_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0;
    v___x_1272_ = l_mkPanicMessageWithDecl(
        v___x_1271_,
        v___x_1270_,
        v___x_1269_,
        v___x_1268_,
        v___x_1267_,
    );
    return v___x_1272_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(
    mut v_a_1273_: *mut leanh::LeanObject,
    mut v_body_1274_: *mut leanh::LeanObject,
    mut v_ys_1275_: *mut leanh::LeanObject,
    mut v_args_1276_: *mut leanh::LeanObject,
    mut v_mask_1277_: *mut leanh::LeanObject,
    mut v___x_1278_: u8,
    mut v_i_1279_: *mut leanh::LeanObject,
    mut v_altType_1280_: *mut leanh::LeanObject,
    mut v_altInfo_1281_: *mut leanh::LeanObject,
    mut v_k_1282_: *mut leanh::LeanObject,
    mut v_y_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
    mut v___y_1286_: *mut leanh::LeanObject,
    mut v___y_1287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1309_: u8 = 0;
    let mut v___x_1310_: u8 = 0;
    let mut v___x_1311_: u8 = 0;
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1318_: usize = 0;
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: usize = 0;
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: u8 = 0;
    let mut v_a_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1289_ = l_Lean_Meta_matchEq_x3f(
                    v_a_1273_,
                    v___y_1284_,
                    v___y_1285_,
                    v___y_1286_,
                    v___y_1287_,
                );
                if leanh::lean_obj_tag(v___x_1289_) == 0 {
                    v_a_1290_ = leanh::lean_ctor_get(v___x_1289_, 0);
                    leanh::lean_inc(v_a_1290_);
                    leanh::lean_dec_ref_known(v___x_1289_, 1);
                    v___x_1291_ = lean_expr_instantiate1(v_body_1274_, v_y_1283_);
                    if leanh::lean_obj_tag(v_a_1290_) == 1 {
                        v_val_1304_ = leanh::lean_ctor_get(v_a_1290_, 0);
                        leanh::lean_inc(v_val_1304_);
                        leanh::lean_dec_ref_known(v_a_1290_, 1);
                        v_snd_1305_ = leanh::lean_ctor_get(v_val_1304_, 1);
                        leanh::lean_inc(v_snd_1305_);
                        leanh::lean_dec(v_val_1304_);
                        v_fst_1306_ = leanh::lean_ctor_get(v_snd_1305_, 0);
                        leanh::lean_inc(v_fst_1306_);
                        v_snd_1307_ = leanh::lean_ctor_get(v_snd_1305_, 1);
                        leanh::lean_inc(v_snd_1307_);
                        leanh::lean_dec(v_snd_1305_);
                        v___x_1364_ = l_Lean_Expr_isFVar(v_fst_1306_);
                        if v___x_1364_ == 0 {
                            v___y_1309_ = v___x_1364_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1365_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_ys_1275_, v_fst_1306_);
                            v___y_1309_ = v___x_1365_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1290_);
                        v___y_1293_ = v___y_1284_;
                        v___y_1294_ = v___y_1285_;
                        v___y_1295_ = v___y_1286_;
                        v___y_1296_ = v___y_1287_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_y_1283_);
                    leanh::lean_dec_ref(v_k_1282_);
                    leanh::lean_dec_ref(v_altInfo_1281_);
                    leanh::lean_dec_ref(v_altType_1280_);
                    leanh::lean_dec_ref(v_mask_1277_);
                    leanh::lean_dec_ref(v_args_1276_);
                    leanh::lean_dec_ref(v_ys_1275_);
                    v_a_1366_ = leanh::lean_ctor_get(v___x_1289_, 0);
                    v_isSharedCheck_1373_ = (!leanh::lean_is_exclusive(v___x_1289_)) as u8;
                    if v_isSharedCheck_1373_ == 0 {
                        v___x_1368_ = v___x_1289_;
                        v_isShared_1369_ = v_isSharedCheck_1373_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1366_);
                        leanh::lean_dec(v___x_1289_);
                        v___x_1368_ = leanh::lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1373_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_y_1283_);
                v___x_1297_ = lean_array_push(v_ys_1275_, v_y_1283_);
                v___x_1298_ = lean_array_push(v_args_1276_, v_y_1283_);
                v___x_1299_ = leanh::lean_box((v___x_1278_) as usize);
                v___x_1300_ = lean_array_push(v_mask_1277_, v___x_1299_);
                v___x_1301_ = leanh::lean_unsigned_to_nat(1);
                v___x_1302_ = lean_nat_add(v_i_1279_, v___x_1301_);
                v___x_1303_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_1280_, v_altInfo_1281_, v_k_1282_, v___x_1297_, v___x_1298_, v___x_1300_, v___x_1302_, v___x_1291_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
                return v___x_1303_;
            }
            2 => {
                if v___y_1309_ == 0 {
                    leanh::lean_dec(v_snd_1307_);
                    leanh::lean_dec(v_fst_1306_);
                    v___y_1293_ = v___y_1284_;
                    v___y_1294_ = v___y_1285_;
                    v___y_1295_ = v___y_1286_;
                    v___y_1296_ = v___y_1287_;
                    state = 1;
                    continue;
                } else {
                    v___x_1310_ = l_Array_contains___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__0(v_args_1276_, v_fst_1306_);
                    if v___x_1310_ == 0 {
                        leanh::lean_dec(v_snd_1307_);
                        leanh::lean_dec(v_fst_1306_);
                        v___y_1293_ = v___y_1284_;
                        v___y_1294_ = v___y_1285_;
                        v___y_1295_ = v___y_1286_;
                        v___y_1296_ = v___y_1287_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_y_1283_);
                        v___x_1311_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_isNamedPatternProof(v___x_1291_, v_y_1283_);
                        if v___x_1311_ == 0 {
                            leanh::lean_dec(v_snd_1307_);
                            leanh::lean_dec(v_fst_1306_);
                            v___y_1293_ = v___y_1284_;
                            v___y_1294_ = v___y_1285_;
                            v___y_1295_ = v___y_1286_;
                            v___y_1296_ = v___y_1287_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1312_ = l_Array_finIdxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__1(v_ys_1275_, v_fst_1306_);
                            if leanh::lean_obj_tag(v___x_1312_) == 1 {
                                v_val_1313_ = leanh::lean_ctor_get(v___x_1312_, 0);
                                leanh::lean_inc(v_val_1313_);
                                leanh::lean_dec_ref_known(v___x_1312_, 1);
                                v___x_1314_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__2(v_args_1276_, v_fst_1306_);
                                if leanh::lean_obj_tag(v___x_1314_) == 1 {
                                    v_val_1315_ = leanh::lean_ctor_get(v___x_1314_, 0);
                                    leanh::lean_inc(v_val_1315_);
                                    leanh::lean_dec_ref_known(v___x_1314_, 1);
                                    leanh::lean_inc(v_snd_1307_);
                                    v___x_1316_ = l_Lean_Meta_mkEqRefl(
                                        v_snd_1307_,
                                        v___y_1284_,
                                        v___y_1285_,
                                        v___y_1286_,
                                        v___y_1287_,
                                    );
                                    if leanh::lean_obj_tag(v___x_1316_) == 0 {
                                        v_a_1317_ = leanh::lean_ctor_get(v___x_1316_, 0);
                                        leanh::lean_inc_n(v_a_1317_, 2);
                                        leanh::lean_dec_ref_known(v___x_1316_, 1);
                                        v_sz_1318_ = lean_array_size(v_args_1276_);
                                        v___x_1319_ =
                                            l_Array_eraseIdx___redArg(v_ys_1275_, v_val_1313_);
                                        v___x_1320_ = 0;
                                        v___x_1321_ =
                                            leanh::lean_box((v___x_1320_) as usize);
                                        v___x_1322_ =
                                            lean_array_set(v_mask_1277_, v_val_1315_, v___x_1321_);
                                        leanh::lean_dec(v_val_1315_);
                                        v___x_1323_ = 0usize;
                                        leanh::lean_inc(v_snd_1307_);
                                        v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__3(v_fst_1306_, v_snd_1307_, v_sz_1318_, v___x_1323_, v_args_1276_);
                                        leanh::lean_inc(v_fst_1306_);
                                        v___x_1325_ = l_Lean_Expr_replaceFVar(
                                            v___x_1291_,
                                            v_fst_1306_,
                                            v_snd_1307_,
                                        );
                                        leanh::lean_dec_ref(v___x_1291_);
                                        v___x_1326_ = l_Lean_Expr_fvarId_x21(v_fst_1306_);
                                        leanh::lean_dec(v_fst_1306_);
                                        v___x_1327_ = l_Lean_Expr_fvarId_x21(v_y_1283_);
                                        leanh::lean_dec_ref(v_y_1283_);
                                        v___x_1328_ = lean_array_push(v___x_1324_, v_a_1317_);
                                        v___x_1329_ =
                                            leanh::lean_box((v___x_1320_) as usize);
                                        v___x_1330_ = lean_array_push(v___x_1322_, v___x_1329_);
                                        v___x_1331_ = leanh::lean_unsigned_to_nat(1);
                                        v___x_1332_ = lean_nat_add(v_i_1279_, v___x_1331_);
                                        v___x_1333_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___boxed as *mut core::ffi::c_void, 13, 8);
                                        leanh::lean_closure_set(
                                            v___x_1333_,
                                            0,
                                            v_altType_1280_,
                                        );
                                        leanh::lean_closure_set(
                                            v___x_1333_,
                                            1,
                                            v_altInfo_1281_,
                                        );
                                        leanh::lean_closure_set(v___x_1333_, 2, v_k_1282_);
                                        leanh::lean_closure_set(v___x_1333_, 3, v___x_1319_);
                                        leanh::lean_closure_set(v___x_1333_, 4, v___x_1328_);
                                        leanh::lean_closure_set(v___x_1333_, 5, v___x_1330_);
                                        leanh::lean_closure_set(v___x_1333_, 6, v___x_1332_);
                                        leanh::lean_closure_set(v___x_1333_, 7, v___x_1325_);
                                        v___x_1334_ = leanh::lean_alloc_closure(
                                            l_Lean_Meta_withReplaceFVarId___boxed
                                                as *mut core::ffi::c_void,
                                            9,
                                            4,
                                        );
                                        leanh::lean_closure_set(
                                            v___x_1334_,
                                            0,
                                            leanh::lean_box(0),
                                        );
                                        leanh::lean_closure_set(v___x_1334_, 1, v___x_1327_);
                                        leanh::lean_closure_set(v___x_1334_, 2, v_a_1317_);
                                        leanh::lean_closure_set(v___x_1334_, 3, v___x_1333_);
                                        v___x_1335_ = l_Lean_Meta_withReplaceFVarId___redArg(
                                            v___x_1326_,
                                            v_snd_1307_,
                                            v___x_1334_,
                                            v___y_1284_,
                                            v___y_1285_,
                                            v___y_1286_,
                                            v___y_1287_,
                                        );
                                        return v___x_1335_;
                                    } else {
                                        leanh::lean_dec(v_val_1315_);
                                        leanh::lean_dec(v_val_1313_);
                                        leanh::lean_dec(v_snd_1307_);
                                        leanh::lean_dec(v_fst_1306_);
                                        leanh::lean_dec_ref(v___x_1291_);
                                        leanh::lean_dec_ref(v_y_1283_);
                                        leanh::lean_dec_ref(v_k_1282_);
                                        leanh::lean_dec_ref(v_altInfo_1281_);
                                        leanh::lean_dec_ref(v_altType_1280_);
                                        leanh::lean_dec_ref(v_mask_1277_);
                                        leanh::lean_dec_ref(v_args_1276_);
                                        leanh::lean_dec_ref(v_ys_1275_);
                                        v_a_1336_ = leanh::lean_ctor_get(v___x_1316_, 0);
                                        v_isSharedCheck_1343_ =
                                            (!leanh::lean_is_exclusive(v___x_1316_)) as u8;
                                        if v_isSharedCheck_1343_ == 0 {
                                            v___x_1338_ = v___x_1316_;
                                            v_isShared_1339_ = v_isSharedCheck_1343_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1336_);
                                            leanh::lean_dec(v___x_1316_);
                                            v___x_1338_ = leanh::lean_box(0);
                                            v_isShared_1339_ = v_isSharedCheck_1343_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v___x_1314_);
                                    leanh::lean_dec(v_val_1313_);
                                    leanh::lean_dec(v_snd_1307_);
                                    leanh::lean_dec(v_fst_1306_);
                                    v___x_1344_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3_once), _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__3);
                                    v___x_1345_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_1344_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
                                    if leanh::lean_obj_tag(v___x_1345_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_1345_, 1);
                                        v___y_1293_ = v___y_1284_;
                                        v___y_1294_ = v___y_1285_;
                                        v___y_1295_ = v___y_1286_;
                                        v___y_1296_ = v___y_1287_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v___x_1291_);
                                        leanh::lean_dec_ref(v_y_1283_);
                                        leanh::lean_dec_ref(v_k_1282_);
                                        leanh::lean_dec_ref(v_altInfo_1281_);
                                        leanh::lean_dec_ref(v_altType_1280_);
                                        leanh::lean_dec_ref(v_mask_1277_);
                                        leanh::lean_dec_ref(v_args_1276_);
                                        leanh::lean_dec_ref(v_ys_1275_);
                                        v_a_1346_ = leanh::lean_ctor_get(v___x_1345_, 0);
                                        v_isSharedCheck_1353_ =
                                            (!leanh::lean_is_exclusive(v___x_1345_)) as u8;
                                        if v_isSharedCheck_1353_ == 0 {
                                            v___x_1348_ = v___x_1345_;
                                            v_isShared_1349_ = v_isSharedCheck_1353_;
                                            state = 5;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1346_);
                                            leanh::lean_dec(v___x_1345_);
                                            v___x_1348_ = leanh::lean_box(0);
                                            v_isShared_1349_ = v_isSharedCheck_1353_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec(v___x_1312_);
                                leanh::lean_dec(v_snd_1307_);
                                leanh::lean_dec(v_fst_1306_);
                                v___x_1354_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4_once), _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__4);
                                v___x_1355_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4(v___x_1354_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
                                if leanh::lean_obj_tag(v___x_1355_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1355_, 1);
                                    v___y_1293_ = v___y_1284_;
                                    v___y_1294_ = v___y_1285_;
                                    v___y_1295_ = v___y_1286_;
                                    v___y_1296_ = v___y_1287_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v___x_1291_);
                                    leanh::lean_dec_ref(v_y_1283_);
                                    leanh::lean_dec_ref(v_k_1282_);
                                    leanh::lean_dec_ref(v_altInfo_1281_);
                                    leanh::lean_dec_ref(v_altType_1280_);
                                    leanh::lean_dec_ref(v_mask_1277_);
                                    leanh::lean_dec_ref(v_args_1276_);
                                    leanh::lean_dec_ref(v_ys_1275_);
                                    v_a_1356_ = leanh::lean_ctor_get(v___x_1355_, 0);
                                    v_isSharedCheck_1363_ =
                                        (!leanh::lean_is_exclusive(v___x_1355_)) as u8;
                                    if v_isSharedCheck_1363_ == 0 {
                                        v___x_1358_ = v___x_1355_;
                                        v_isShared_1359_ = v_isSharedCheck_1363_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1356_);
                                        leanh::lean_dec(v___x_1355_);
                                        v___x_1358_ = leanh::lean_box(0);
                                        v_isShared_1359_ = v_isSharedCheck_1363_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_1339_ == 0 {
                    v___x_1341_ = v___x_1338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1341_;
            }
            5 => {
                if v_isShared_1349_ == 0 {
                    v___x_1351_ = v___x_1348_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1352_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
                    v___x_1351_ = v_reuseFailAlloc_1352_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1351_;
            }
            7 => {
                if v_isShared_1359_ == 0 {
                    v___x_1361_ = v___x_1358_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
                    v___x_1361_ = v_reuseFailAlloc_1362_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1361_;
            }
            9 => {
                if v_isShared_1369_ == 0 {
                    v___x_1371_ = v___x_1368_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1372_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
                    v___x_1371_ = v_reuseFailAlloc_1372_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed(
    mut v_a_1374_: *mut leanh::LeanObject,
    mut v_body_1375_: *mut leanh::LeanObject,
    mut v_ys_1376_: *mut leanh::LeanObject,
    mut v_args_1377_: *mut leanh::LeanObject,
    mut v_mask_1378_: *mut leanh::LeanObject,
    mut v___x_1379_: *mut leanh::LeanObject,
    mut v_i_1380_: *mut leanh::LeanObject,
    mut v_altType_1381_: *mut leanh::LeanObject,
    mut v_altInfo_1382_: *mut leanh::LeanObject,
    mut v_k_1383_: *mut leanh::LeanObject,
    mut v_y_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
    mut v___y_1387_: *mut leanh::LeanObject,
    mut v___y_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4447__boxed_1390_: u8 = 0;
    let mut v_res_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4447__boxed_1390_ = (leanh::lean_unbox(v___x_1379_) as u8);
    v_res_1391_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0(v_a_1374_, v_body_1375_, v_ys_1376_, v_args_1377_, v_mask_1378_, v___x_4447__boxed_1390_, v_i_1380_, v_altType_1381_, v_altInfo_1382_, v_k_1383_, v_y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
    leanh::lean_dec(v___y_1388_);
    leanh::lean_dec_ref(v___y_1387_);
    leanh::lean_dec(v___y_1386_);
    leanh::lean_dec_ref(v___y_1385_);
    leanh::lean_dec(v_i_1380_);
    leanh::lean_dec_ref(v_body_1375_);
    return v_res_1391_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(
    mut v_altType_1392_: *mut leanh::LeanObject,
    mut v_altInfo_1393_: *mut leanh::LeanObject,
    mut v_k_1394_: *mut leanh::LeanObject,
    mut v_ys_1395_: *mut leanh::LeanObject,
    mut v_args_1396_: *mut leanh::LeanObject,
    mut v_mask_1397_: *mut leanh::LeanObject,
    mut v_i_1398_: *mut leanh::LeanObject,
    mut v_type_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
    mut v_a_1401_: *mut leanh::LeanObject,
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut v_binderName_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1431_: u8 = 0;
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1435_: u8 = 0;
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1405_ = l_Lean_Meta_whnfForall(
                    v_type_1399_,
                    v_a_1400_,
                    v_a_1401_,
                    v_a_1402_,
                    v_a_1403_,
                );
                if leanh::lean_obj_tag(v___x_1405_) == 0 {
                    v_a_1406_ = leanh::lean_ctor_get(v___x_1405_, 0);
                    leanh::lean_inc(v_a_1406_);
                    leanh::lean_dec_ref_known(v___x_1405_, 1);
                    v_numFields_1407_ = leanh::lean_ctor_get(v_altInfo_1393_, 0);
                    v___x_1408_ = lean_nat_dec_lt(v_i_1398_, v_numFields_1407_);
                    if v___x_1408_ == 0 {
                        leanh::lean_dec(v_i_1398_);
                        leanh::lean_dec_ref(v_altInfo_1393_);
                        leanh::lean_dec_ref(v_altType_1392_);
                        v___x_1409_ = l_Lean_Meta_Match_unfoldNamedPattern(
                            v_a_1406_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_,
                        );
                        if leanh::lean_obj_tag(v___x_1409_) == 0 {
                            v_a_1410_ = leanh::lean_ctor_get(v___x_1409_, 0);
                            leanh::lean_inc(v_a_1410_);
                            leanh::lean_dec_ref_known(v___x_1409_, 1);
                            leanh::lean_inc(v_a_1403_);
                            leanh::lean_inc_ref(v_a_1402_);
                            leanh::lean_inc(v_a_1401_);
                            leanh::lean_inc_ref(v_a_1400_);
                            v___x_1411_ = leanh::lean_apply_9(
                                v_k_1394_,
                                v_ys_1395_,
                                v_args_1396_,
                                v_mask_1397_,
                                v_a_1410_,
                                v_a_1400_,
                                v_a_1401_,
                                v_a_1402_,
                                v_a_1403_,
                                leanh::lean_box(0),
                            );
                            return v___x_1411_;
                        } else {
                            leanh::lean_dec_ref(v_mask_1397_);
                            leanh::lean_dec_ref(v_args_1396_);
                            leanh::lean_dec_ref(v_ys_1395_);
                            leanh::lean_dec_ref(v_k_1394_);
                            v_a_1412_ = leanh::lean_ctor_get(v___x_1409_, 0);
                            v_isSharedCheck_1419_ =
                                (!leanh::lean_is_exclusive(v___x_1409_)) as u8;
                            if v_isSharedCheck_1419_ == 0 {
                                v___x_1414_ = v___x_1409_;
                                v_isShared_1415_ = v_isSharedCheck_1419_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1412_);
                                leanh::lean_dec(v___x_1409_);
                                v___x_1414_ = leanh::lean_box(0);
                                v_isShared_1415_ = v_isSharedCheck_1419_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v_a_1406_) == 7 {
                            v_binderName_1420_ = leanh::lean_ctor_get(v_a_1406_, 0);
                            leanh::lean_inc(v_binderName_1420_);
                            v_binderType_1421_ = leanh::lean_ctor_get(v_a_1406_, 1);
                            leanh::lean_inc_ref(v_binderType_1421_);
                            v_body_1422_ = leanh::lean_ctor_get(v_a_1406_, 2);
                            leanh::lean_inc_ref(v_body_1422_);
                            leanh::lean_dec_ref_known(v_a_1406_, 3);
                            v___x_1423_ = l_Lean_Meta_Match_unfoldNamedPattern(
                                v_binderType_1421_,
                                v_a_1400_,
                                v_a_1401_,
                                v_a_1402_,
                                v_a_1403_,
                            );
                            if leanh::lean_obj_tag(v___x_1423_) == 0 {
                                v_a_1424_ = leanh::lean_ctor_get(v___x_1423_, 0);
                                leanh::lean_inc_n(v_a_1424_, 2);
                                leanh::lean_dec_ref_known(v___x_1423_, 1);
                                v___x_1425_ = leanh::lean_box((v___x_1408_) as usize);
                                v___f_1426_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 16, 10);
                                leanh::lean_closure_set(v___f_1426_, 0, v_a_1424_);
                                leanh::lean_closure_set(v___f_1426_, 1, v_body_1422_);
                                leanh::lean_closure_set(v___f_1426_, 2, v_ys_1395_);
                                leanh::lean_closure_set(v___f_1426_, 3, v_args_1396_);
                                leanh::lean_closure_set(v___f_1426_, 4, v_mask_1397_);
                                leanh::lean_closure_set(v___f_1426_, 5, v___x_1425_);
                                leanh::lean_closure_set(v___f_1426_, 6, v_i_1398_);
                                leanh::lean_closure_set(v___f_1426_, 7, v_altType_1392_);
                                leanh::lean_closure_set(v___f_1426_, 8, v_altInfo_1393_);
                                leanh::lean_closure_set(v___f_1426_, 9, v_k_1394_);
                                v___x_1427_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_1420_, v_a_1424_, v___f_1426_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
                                return v___x_1427_;
                            } else {
                                leanh::lean_dec_ref(v_body_1422_);
                                leanh::lean_dec(v_binderName_1420_);
                                leanh::lean_dec(v_i_1398_);
                                leanh::lean_dec_ref(v_mask_1397_);
                                leanh::lean_dec_ref(v_args_1396_);
                                leanh::lean_dec_ref(v_ys_1395_);
                                leanh::lean_dec_ref(v_k_1394_);
                                leanh::lean_dec_ref(v_altInfo_1393_);
                                leanh::lean_dec_ref(v_altType_1392_);
                                v_a_1428_ = leanh::lean_ctor_get(v___x_1423_, 0);
                                v_isSharedCheck_1435_ =
                                    (!leanh::lean_is_exclusive(v___x_1423_)) as u8;
                                if v_isSharedCheck_1435_ == 0 {
                                    v___x_1430_ = v___x_1423_;
                                    v_isShared_1431_ = v_isSharedCheck_1435_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1428_);
                                    leanh::lean_dec(v___x_1423_);
                                    v___x_1430_ = leanh::lean_box(0);
                                    v_isShared_1431_ = v_isSharedCheck_1435_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_inc(v_numFields_1407_);
                            leanh::lean_dec(v_a_1406_);
                            leanh::lean_dec(v_i_1398_);
                            leanh::lean_dec_ref(v_mask_1397_);
                            leanh::lean_dec_ref(v_args_1396_);
                            leanh::lean_dec_ref(v_ys_1395_);
                            leanh::lean_dec_ref(v_k_1394_);
                            leanh::lean_dec_ref(v_altInfo_1393_);
                            v___x_1436_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
                            v___x_1437_ = l_Nat_reprFast(v_numFields_1407_);
                            v___x_1438_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1438_, 0, v___x_1437_);
                            v___x_1439_ = l_Lean_MessageData_ofFormat(v___x_1438_);
                            v___x_1440_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1440_, 0, v___x_1436_);
                            leanh::lean_ctor_set(v___x_1440_, 1, v___x_1439_);
                            v___x_1441_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3_once), _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__3);
                            v___x_1442_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1442_, 0, v___x_1440_);
                            leanh::lean_ctor_set(v___x_1442_, 1, v___x_1441_);
                            v___x_1443_ = l_Lean_indentExpr(v_altType_1392_);
                            v___x_1444_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1444_, 0, v___x_1442_);
                            leanh::lean_ctor_set(v___x_1444_, 1, v___x_1443_);
                            v___x_1445_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_1444_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
                            return v___x_1445_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_i_1398_);
                    leanh::lean_dec_ref(v_mask_1397_);
                    leanh::lean_dec_ref(v_args_1396_);
                    leanh::lean_dec_ref(v_ys_1395_);
                    leanh::lean_dec_ref(v_k_1394_);
                    leanh::lean_dec_ref(v_altInfo_1393_);
                    leanh::lean_dec_ref(v_altType_1392_);
                    v_a_1446_ = leanh::lean_ctor_get(v___x_1405_, 0);
                    v_isSharedCheck_1453_ = (!leanh::lean_is_exclusive(v___x_1405_)) as u8;
                    if v_isSharedCheck_1453_ == 0 {
                        v___x_1448_ = v___x_1405_;
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1446_);
                        leanh::lean_dec(v___x_1405_);
                        v___x_1448_ = leanh::lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1415_ == 0 {
                    v___x_1417_ = v___x_1414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
                    v___x_1417_ = v_reuseFailAlloc_1418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1417_;
            }
            3 => {
                if v_isShared_1431_ == 0 {
                    v___x_1433_ = v___x_1430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1434_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
                    v___x_1433_ = v_reuseFailAlloc_1434_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1433_;
            }
            5 => {
                if v_isShared_1449_ == 0 {
                    v___x_1451_ = v___x_1448_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
                    v___x_1451_ = v_reuseFailAlloc_1452_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(
    mut v_00_u03b1_1454_: *mut leanh::LeanObject,
    mut v_altType_1455_: *mut leanh::LeanObject,
    mut v_altInfo_1456_: *mut leanh::LeanObject,
    mut v_k_1457_: *mut leanh::LeanObject,
    mut v_ys_1458_: *mut leanh::LeanObject,
    mut v_args_1459_: *mut leanh::LeanObject,
    mut v_mask_1460_: *mut leanh::LeanObject,
    mut v_i_1461_: *mut leanh::LeanObject,
    mut v_type_1462_: *mut leanh::LeanObject,
    mut v_a_1463_: *mut leanh::LeanObject,
    mut v_a_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
    mut v_a_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1468_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_1455_, v_altInfo_1456_, v_k_1457_, v_ys_1458_, v_args_1459_, v_mask_1460_, v_i_1461_, v_type_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
    return v___x_1468_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___boxed(
    mut v_00_u03b1_1469_: *mut leanh::LeanObject,
    mut v_altType_1470_: *mut leanh::LeanObject,
    mut v_altInfo_1471_: *mut leanh::LeanObject,
    mut v_k_1472_: *mut leanh::LeanObject,
    mut v_ys_1473_: *mut leanh::LeanObject,
    mut v_args_1474_: *mut leanh::LeanObject,
    mut v_mask_1475_: *mut leanh::LeanObject,
    mut v_i_1476_: *mut leanh::LeanObject,
    mut v_type_1477_: *mut leanh::LeanObject,
    mut v_a_1478_: *mut leanh::LeanObject,
    mut v_a_1479_: *mut leanh::LeanObject,
    mut v_a_1480_: *mut leanh::LeanObject,
    mut v_a_1481_: *mut leanh::LeanObject,
    mut v_a_1482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1483_ =
        l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go(
            v_00_u03b1_1469_,
            v_altType_1470_,
            v_altInfo_1471_,
            v_k_1472_,
            v_ys_1473_,
            v_args_1474_,
            v_mask_1475_,
            v_i_1476_,
            v_type_1477_,
            v_a_1478_,
            v_a_1479_,
            v_a_1480_,
            v_a_1481_,
        );
    leanh::lean_dec(v_a_1481_);
    leanh::lean_dec_ref(v_a_1480_);
    leanh::lean_dec(v_a_1479_);
    leanh::lean_dec_ref(v_a_1478_);
    return v_res_1483_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(
    mut v_00_u03b1_1484_: *mut leanh::LeanObject,
    mut v_name_1485_: *mut leanh::LeanObject,
    mut v_bi_1486_: u8,
    mut v_type_1487_: *mut leanh::LeanObject,
    mut v_k_1488_: *mut leanh::LeanObject,
    mut v_kind_1489_: u8,
    mut v___y_1490_: *mut leanh::LeanObject,
    mut v___y_1491_: *mut leanh::LeanObject,
    mut v___y_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___redArg(v_name_1485_, v_bi_1486_, v_type_1487_, v_k_1488_, v_kind_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
    return v___x_1495_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7___boxed(
    mut v_00_u03b1_1496_: *mut leanh::LeanObject,
    mut v_name_1497_: *mut leanh::LeanObject,
    mut v_bi_1498_: *mut leanh::LeanObject,
    mut v_type_1499_: *mut leanh::LeanObject,
    mut v_k_1500_: *mut leanh::LeanObject,
    mut v_kind_1501_: *mut leanh::LeanObject,
    mut v___y_1502_: *mut leanh::LeanObject,
    mut v___y_1503_: *mut leanh::LeanObject,
    mut v___y_1504_: *mut leanh::LeanObject,
    mut v___y_1505_: *mut leanh::LeanObject,
    mut v___y_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_1507_: u8 = 0;
    let mut v_kind_boxed_1508_: u8 = 0;
    let mut v_res_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1507_ = (leanh::lean_unbox(v_bi_1498_) as u8);
    v_kind_boxed_1508_ = (leanh::lean_unbox(v_kind_1501_) as u8);
    v_res_1509_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5_spec__7(v_00_u03b1_1496_, v_name_1497_, v_bi_boxed_1507_, v_type_1499_, v_k_1500_, v_kind_boxed_1508_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
    leanh::lean_dec(v___y_1505_);
    leanh::lean_dec_ref(v___y_1504_);
    leanh::lean_dec(v___y_1503_);
    leanh::lean_dec_ref(v___y_1502_);
    return v_res_1509_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(
    mut v_00_u03b1_1510_: *mut leanh::LeanObject,
    mut v_name_1511_: *mut leanh::LeanObject,
    mut v_type_1512_: *mut leanh::LeanObject,
    mut v_k_1513_: *mut leanh::LeanObject,
    mut v___y_1514_: *mut leanh::LeanObject,
    mut v___y_1515_: *mut leanh::LeanObject,
    mut v___y_1516_: *mut leanh::LeanObject,
    mut v___y_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_name_1511_, v_type_1512_, v_k_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
    return v___x_1519_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___boxed(
    mut v_00_u03b1_1520_: *mut leanh::LeanObject,
    mut v_name_1521_: *mut leanh::LeanObject,
    mut v_type_1522_: *mut leanh::LeanObject,
    mut v_k_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
    mut v___y_1526_: *mut leanh::LeanObject,
    mut v___y_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5(v_00_u03b1_1520_, v_name_1521_, v_type_1522_, v_k_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
    leanh::lean_dec(v___y_1527_);
    leanh::lean_dec_ref(v___y_1526_);
    leanh::lean_dec(v___y_1525_);
    leanh::lean_dec_ref(v___y_1524_);
    return v_res_1529_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(
    mut v_00_u03b1_1530_: *mut leanh::LeanObject,
    mut v_msg_1531_: *mut leanh::LeanObject,
    mut v___y_1532_: *mut leanh::LeanObject,
    mut v___y_1533_: *mut leanh::LeanObject,
    mut v___y_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v_msg_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
    return v___x_1537_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___boxed(
    mut v_00_u03b1_1538_: *mut leanh::LeanObject,
    mut v_msg_1539_: *mut leanh::LeanObject,
    mut v___y_1540_: *mut leanh::LeanObject,
    mut v___y_1541_: *mut leanh::LeanObject,
    mut v___y_1542_: *mut leanh::LeanObject,
    mut v___y_1543_: *mut leanh::LeanObject,
    mut v___y_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1545_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6(v_00_u03b1_1538_, v_msg_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
    leanh::lean_dec(v___y_1543_);
    leanh::lean_dec_ref(v___y_1542_);
    leanh::lean_dec(v___y_1541_);
    leanh::lean_dec_ref(v___y_1540_);
    return v_res_1545_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(
    mut v_msg_1546_: *mut leanh::LeanObject,
    mut v___y_1547_: *mut leanh::LeanObject,
    mut v___y_1548_: *mut leanh::LeanObject,
    mut v___y_1549_: *mut leanh::LeanObject,
    mut v___y_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500__overap_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1552_ = l_panic___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__4___closed__0;
    v___x_500__overap_1553_ = lean_panic_fn_borrowed(v___f_1552_, v_msg_1546_);
    leanh::lean_inc(v___y_1550_);
    leanh::lean_inc_ref(v___y_1549_);
    leanh::lean_inc(v___y_1548_);
    leanh::lean_inc_ref(v___y_1547_);
    v___x_1554_ = leanh::lean_apply_5(
        v___x_500__overap_1553_,
        v___y_1547_,
        v___y_1548_,
        v___y_1549_,
        v___y_1550_,
        leanh::lean_box(0),
    );
    return v___x_1554_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg___boxed(
    mut v_msg_1555_: *mut leanh::LeanObject,
    mut v___y_1556_: *mut leanh::LeanObject,
    mut v___y_1557_: *mut leanh::LeanObject,
    mut v___y_1558_: *mut leanh::LeanObject,
    mut v___y_1559_: *mut leanh::LeanObject,
    mut v___y_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(
        v_msg_1555_,
        v___y_1556_,
        v___y_1557_,
        v___y_1558_,
        v___y_1559_,
    );
    leanh::lean_dec(v___y_1559_);
    leanh::lean_dec_ref(v___y_1558_);
    leanh::lean_dec(v___y_1557_);
    leanh::lean_dec_ref(v___y_1556_);
    return v_res_1561_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(
    mut v_00_u03b1_1562_: *mut leanh::LeanObject,
    mut v_msg_1563_: *mut leanh::LeanObject,
    mut v___y_1564_: *mut leanh::LeanObject,
    mut v___y_1565_: *mut leanh::LeanObject,
    mut v___y_1566_: *mut leanh::LeanObject,
    mut v___y_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1569_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(
        v_msg_1563_,
        v___y_1564_,
        v___y_1565_,
        v___y_1566_,
        v___y_1567_,
    );
    return v___x_1569_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___boxed(
    mut v_00_u03b1_1570_: *mut leanh::LeanObject,
    mut v_msg_1571_: *mut leanh::LeanObject,
    mut v___y_1572_: *mut leanh::LeanObject,
    mut v___y_1573_: *mut leanh::LeanObject,
    mut v___y_1574_: *mut leanh::LeanObject,
    mut v___y_1575_: *mut leanh::LeanObject,
    mut v___y_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1577_ = l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0(
        v_00_u03b1_1570_,
        v_msg_1571_,
        v___y_1572_,
        v___y_1573_,
        v___y_1574_,
        v___y_1575_,
    );
    leanh::lean_dec(v___y_1575_);
    leanh::lean_dec_ref(v___y_1574_);
    leanh::lean_dec(v___y_1573_);
    leanh::lean_dec_ref(v___y_1572_);
    return v_res_1577_;
}
pub unsafe fn _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__1;
    v___x_1581_ = leanh::lean_unsigned_to_nat(2);
    v___x_1582_ = leanh::lean_unsigned_to_nat(45);
    v___x_1583_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__0;
    v___x_1584_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___lam__0___closed__0;
    v___x_1585_ = l_mkPanicMessageWithDecl(
        v___x_1584_,
        v___x_1583_,
        v___x_1582_,
        v___x_1581_,
        v___x_1580_,
    );
    return v___x_1585_;
}
pub unsafe fn _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = leanh::lean_box(0);
    v___x_1594_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__6;
    v___x_1595_ = l_Lean_mkConst(v___x_1594_, v___x_1593_);
    return v___x_1595_;
}
pub unsafe fn _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1596_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7_once),
        _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__7,
    );
    v___x_1597_ = leanh::lean_unsigned_to_nat(1);
    v___x_1598_ = lean_mk_empty_array_with_capacity(v___x_1597_);
    v___x_1599_ = lean_array_push(v___x_1598_, v___x_1596_);
    return v___x_1599_;
}
pub unsafe fn l_Lean_Meta_Match_forallAltVarsTelescope___redArg(
    mut v_altType_1605_: *mut leanh::LeanObject,
    mut v_altInfo_1606_: *mut leanh::LeanObject,
    mut v_k_1607_: *mut leanh::LeanObject,
    mut v_a_1608_: *mut leanh::LeanObject,
    mut v_a_1609_: *mut leanh::LeanObject,
    mut v_a_1610_: *mut leanh::LeanObject,
    mut v_a_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numOverlaps_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasUnitThunk_1614_: u8 = 0;
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: u8 = 0;
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut v_a_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut v_a_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1650_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numOverlaps_1613_ = leanh::lean_ctor_get(v_altInfo_1606_, 1);
                v_hasUnitThunk_1614_ = leanh::lean_ctor_get_uint8(
                    v_altInfo_1606_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v___x_1615_ = leanh::lean_unsigned_to_nat(0);
                v___x_1616_ = lean_nat_dec_eq(v_numOverlaps_1613_, v___x_1615_);
                if v___x_1616_ == 0 {
                    leanh::lean_dec_ref(v_k_1607_);
                    leanh::lean_dec_ref(v_altInfo_1606_);
                    leanh::lean_dec_ref(v_altType_1605_);
                    v___x_1617_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2_once
                        ),
                        _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__2,
                    );
                    v___x_1618_ =
                        l_panic___at___00Lean_Meta_Match_forallAltVarsTelescope_spec__0___redArg(
                            v___x_1617_,
                            v_a_1608_,
                            v_a_1609_,
                            v_a_1610_,
                            v_a_1611_,
                        );
                    return v___x_1618_;
                } else {
                    if v_hasUnitThunk_1614_ == 0 {
                        v___x_1619_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3;
                        leanh::lean_inc_ref(v_altType_1605_);
                        v___x_1620_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg(v_altType_1605_, v_altInfo_1606_, v_k_1607_, v___x_1619_, v___x_1619_, v___x_1619_, v___x_1615_, v_altType_1605_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
                        return v___x_1620_;
                    } else {
                        leanh::lean_dec_ref(v_altInfo_1606_);
                        v___x_1621_ = l_Lean_Meta_whnfForall(
                            v_altType_1605_,
                            v_a_1608_,
                            v_a_1609_,
                            v_a_1610_,
                            v_a_1611_,
                        );
                        if leanh::lean_obj_tag(v___x_1621_) == 0 {
                            v_a_1622_ = leanh::lean_ctor_get(v___x_1621_, 0);
                            leanh::lean_inc(v_a_1622_);
                            leanh::lean_dec_ref_known(v___x_1621_, 1);
                            v___x_1623_ = l_Lean_Meta_Match_unfoldNamedPattern(
                                v_a_1622_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_,
                            );
                            if leanh::lean_obj_tag(v___x_1623_) == 0 {
                                v_a_1624_ = leanh::lean_ctor_get(v___x_1623_, 0);
                                leanh::lean_inc(v_a_1624_);
                                leanh::lean_dec_ref_known(v___x_1623_, 1);
                                v___x_1625_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8_once), _init_l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__8);
                                v___x_1626_ = l_Lean_Meta_instantiateForall(
                                    v_a_1624_,
                                    v___x_1625_,
                                    v_a_1608_,
                                    v_a_1609_,
                                    v_a_1610_,
                                    v_a_1611_,
                                );
                                if leanh::lean_obj_tag(v___x_1626_) == 0 {
                                    v_a_1627_ = leanh::lean_ctor_get(v___x_1626_, 0);
                                    leanh::lean_inc(v_a_1627_);
                                    leanh::lean_dec_ref_known(v___x_1626_, 1);
                                    v___x_1628_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3;
                                    v___x_1629_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__9;
                                    leanh::lean_inc(v_a_1611_);
                                    leanh::lean_inc_ref(v_a_1610_);
                                    leanh::lean_inc(v_a_1609_);
                                    leanh::lean_inc_ref(v_a_1608_);
                                    v___x_1630_ = leanh::lean_apply_9(
                                        v_k_1607_,
                                        v___x_1628_,
                                        v___x_1625_,
                                        v___x_1629_,
                                        v_a_1627_,
                                        v_a_1608_,
                                        v_a_1609_,
                                        v_a_1610_,
                                        v_a_1611_,
                                        leanh::lean_box(0),
                                    );
                                    return v___x_1630_;
                                } else {
                                    leanh::lean_dec_ref(v_k_1607_);
                                    v_a_1631_ = leanh::lean_ctor_get(v___x_1626_, 0);
                                    v_isSharedCheck_1638_ =
                                        (!leanh::lean_is_exclusive(v___x_1626_)) as u8;
                                    if v_isSharedCheck_1638_ == 0 {
                                        v___x_1633_ = v___x_1626_;
                                        v_isShared_1634_ = v_isSharedCheck_1638_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1631_);
                                        leanh::lean_dec(v___x_1626_);
                                        v___x_1633_ = leanh::lean_box(0);
                                        v_isShared_1634_ = v_isSharedCheck_1638_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_k_1607_);
                                v_a_1639_ = leanh::lean_ctor_get(v___x_1623_, 0);
                                v_isSharedCheck_1646_ =
                                    (!leanh::lean_is_exclusive(v___x_1623_)) as u8;
                                if v_isSharedCheck_1646_ == 0 {
                                    v___x_1641_ = v___x_1623_;
                                    v_isShared_1642_ = v_isSharedCheck_1646_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1639_);
                                    leanh::lean_dec(v___x_1623_);
                                    v___x_1641_ = leanh::lean_box(0);
                                    v_isShared_1642_ = v_isSharedCheck_1646_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_k_1607_);
                            v_a_1647_ = leanh::lean_ctor_get(v___x_1621_, 0);
                            v_isSharedCheck_1654_ =
                                (!leanh::lean_is_exclusive(v___x_1621_)) as u8;
                            if v_isSharedCheck_1654_ == 0 {
                                v___x_1649_ = v___x_1621_;
                                v_isShared_1650_ = v_isSharedCheck_1654_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1647_);
                                leanh::lean_dec(v___x_1621_);
                                v___x_1649_ = leanh::lean_box(0);
                                v_isShared_1650_ = v_isSharedCheck_1654_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1634_ == 0 {
                    v___x_1636_ = v___x_1633_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1637_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
                    v___x_1636_ = v_reuseFailAlloc_1637_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1636_;
            }
            3 => {
                if v_isShared_1642_ == 0 {
                    v___x_1644_ = v___x_1641_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
                    v___x_1644_ = v_reuseFailAlloc_1645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1644_;
            }
            5 => {
                if v_isShared_1650_ == 0 {
                    v___x_1652_ = v___x_1649_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
                    v___x_1652_ = v_reuseFailAlloc_1653_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_forallAltVarsTelescope___redArg___boxed(
    mut v_altType_1655_: *mut leanh::LeanObject,
    mut v_altInfo_1656_: *mut leanh::LeanObject,
    mut v_k_1657_: *mut leanh::LeanObject,
    mut v_a_1658_: *mut leanh::LeanObject,
    mut v_a_1659_: *mut leanh::LeanObject,
    mut v_a_1660_: *mut leanh::LeanObject,
    mut v_a_1661_: *mut leanh::LeanObject,
    mut v_a_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(
        v_altType_1655_,
        v_altInfo_1656_,
        v_k_1657_,
        v_a_1658_,
        v_a_1659_,
        v_a_1660_,
        v_a_1661_,
    );
    leanh::lean_dec(v_a_1661_);
    leanh::lean_dec_ref(v_a_1660_);
    leanh::lean_dec(v_a_1659_);
    leanh::lean_dec_ref(v_a_1658_);
    return v_res_1663_;
}
pub unsafe fn l_Lean_Meta_Match_forallAltVarsTelescope(
    mut v_00_u03b1_1664_: *mut leanh::LeanObject,
    mut v_altType_1665_: *mut leanh::LeanObject,
    mut v_altInfo_1666_: *mut leanh::LeanObject,
    mut v_k_1667_: *mut leanh::LeanObject,
    mut v_a_1668_: *mut leanh::LeanObject,
    mut v_a_1669_: *mut leanh::LeanObject,
    mut v_a_1670_: *mut leanh::LeanObject,
    mut v_a_1671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(
        v_altType_1665_,
        v_altInfo_1666_,
        v_k_1667_,
        v_a_1668_,
        v_a_1669_,
        v_a_1670_,
        v_a_1671_,
    );
    return v___x_1673_;
}
pub unsafe fn l_Lean_Meta_Match_forallAltVarsTelescope___boxed(
    mut v_00_u03b1_1674_: *mut leanh::LeanObject,
    mut v_altType_1675_: *mut leanh::LeanObject,
    mut v_altInfo_1676_: *mut leanh::LeanObject,
    mut v_k_1677_: *mut leanh::LeanObject,
    mut v_a_1678_: *mut leanh::LeanObject,
    mut v_a_1679_: *mut leanh::LeanObject,
    mut v_a_1680_: *mut leanh::LeanObject,
    mut v_a_1681_: *mut leanh::LeanObject,
    mut v_a_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1683_ = l_Lean_Meta_Match_forallAltVarsTelescope(
        v_00_u03b1_1674_,
        v_altType_1675_,
        v_altInfo_1676_,
        v_k_1677_,
        v_a_1678_,
        v_a_1679_,
        v_a_1680_,
        v_a_1681_,
    );
    leanh::lean_dec(v_a_1681_);
    leanh::lean_dec_ref(v_a_1680_);
    leanh::lean_dec(v_a_1679_);
    leanh::lean_dec_ref(v_a_1678_);
    return v_res_1683_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed(
    mut v_body_1684_: *mut leanh::LeanObject,
    mut v_eqs_1685_: *mut leanh::LeanObject,
    mut v_args_1686_: *mut leanh::LeanObject,
    mut v_arg_1687_: *mut leanh::LeanObject,
    mut v_mask_1688_: *mut leanh::LeanObject,
    mut v_i_1689_: *mut leanh::LeanObject,
    mut v_altType_1690_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1691_: *mut leanh::LeanObject,
    mut v_k_1692_: *mut leanh::LeanObject,
    mut v_ys_1693_: *mut leanh::LeanObject,
    mut v_eq_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1700_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(v_body_1684_, v_eqs_1685_, v_args_1686_, v_arg_1687_, v_mask_1688_, v_i_1689_, v_altType_1690_, v_numDiscrEqs_1691_, v_k_1692_, v_ys_1693_, v_eq_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
    leanh::lean_dec(v___y_1698_);
    leanh::lean_dec_ref(v___y_1697_);
    leanh::lean_dec(v___y_1696_);
    leanh::lean_dec_ref(v___y_1695_);
    leanh::lean_dec(v_i_1689_);
    leanh::lean_dec_ref(v_body_1684_);
    return v_res_1700_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__0;
    v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
    return v___x_1703_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__2;
    v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
    return v___x_1706_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(
    mut v_altType_1707_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1708_: *mut leanh::LeanObject,
    mut v_k_1709_: *mut leanh::LeanObject,
    mut v_ys_1710_: *mut leanh::LeanObject,
    mut v_eqs_1711_: *mut leanh::LeanObject,
    mut v_args_1712_: *mut leanh::LeanObject,
    mut v_mask_1713_: *mut leanh::LeanObject,
    mut v_i_1714_: *mut leanh::LeanObject,
    mut v_type_1715_: *mut leanh::LeanObject,
    mut v_a_1716_: *mut leanh::LeanObject,
    mut v_a_1717_: *mut leanh::LeanObject,
    mut v_a_1718_: *mut leanh::LeanObject,
    mut v_a_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: u8 = 0;
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1734_: u8 = 0;
    let mut v_binderName_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1756_: u8 = 0;
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1760_: u8 = 0;
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1785_: u8 = 0;
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1789_: u8 = 0;
    let mut v_a_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut v_a_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1801_: u8 = 0;
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1721_ = l_Lean_Meta_whnfForall(
                    v_type_1715_,
                    v_a_1716_,
                    v_a_1717_,
                    v_a_1718_,
                    v_a_1719_,
                );
                if leanh::lean_obj_tag(v___x_1721_) == 0 {
                    v_a_1722_ = leanh::lean_ctor_get(v___x_1721_, 0);
                    leanh::lean_inc(v_a_1722_);
                    leanh::lean_dec_ref_known(v___x_1721_, 1);
                    v___x_1723_ = lean_nat_dec_lt(v_i_1714_, v_numDiscrEqs_1708_);
                    if v___x_1723_ == 0 {
                        leanh::lean_dec(v_i_1714_);
                        leanh::lean_dec(v_numDiscrEqs_1708_);
                        leanh::lean_dec_ref(v_altType_1707_);
                        v___x_1724_ = l_Lean_Meta_Match_unfoldNamedPattern(
                            v_a_1722_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_,
                        );
                        if leanh::lean_obj_tag(v___x_1724_) == 0 {
                            v_a_1725_ = leanh::lean_ctor_get(v___x_1724_, 0);
                            leanh::lean_inc(v_a_1725_);
                            leanh::lean_dec_ref_known(v___x_1724_, 1);
                            leanh::lean_inc(v_a_1719_);
                            leanh::lean_inc_ref(v_a_1718_);
                            leanh::lean_inc(v_a_1717_);
                            leanh::lean_inc_ref(v_a_1716_);
                            v___x_1726_ = leanh::lean_apply_10(
                                v_k_1709_,
                                v_ys_1710_,
                                v_eqs_1711_,
                                v_args_1712_,
                                v_mask_1713_,
                                v_a_1725_,
                                v_a_1716_,
                                v_a_1717_,
                                v_a_1718_,
                                v_a_1719_,
                                leanh::lean_box(0),
                            );
                            return v___x_1726_;
                        } else {
                            leanh::lean_dec_ref(v_mask_1713_);
                            leanh::lean_dec_ref(v_args_1712_);
                            leanh::lean_dec_ref(v_eqs_1711_);
                            leanh::lean_dec_ref(v_ys_1710_);
                            leanh::lean_dec_ref(v_k_1709_);
                            v_a_1727_ = leanh::lean_ctor_get(v___x_1724_, 0);
                            v_isSharedCheck_1734_ =
                                (!leanh::lean_is_exclusive(v___x_1724_)) as u8;
                            if v_isSharedCheck_1734_ == 0 {
                                v___x_1729_ = v___x_1724_;
                                v_isShared_1730_ = v_isSharedCheck_1734_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1727_);
                                leanh::lean_dec(v___x_1724_);
                                v___x_1729_ = leanh::lean_box(0);
                                v_isShared_1730_ = v_isSharedCheck_1734_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v_a_1722_) == 7 {
                            v_binderName_1735_ = leanh::lean_ctor_get(v_a_1722_, 0);
                            leanh::lean_inc(v_binderName_1735_);
                            v_binderType_1736_ = leanh::lean_ctor_get(v_a_1722_, 1);
                            leanh::lean_inc_ref_n(v_binderType_1736_, 2);
                            v_body_1737_ = leanh::lean_ctor_get(v_a_1722_, 2);
                            leanh::lean_inc_ref(v_body_1737_);
                            leanh::lean_dec_ref_known(v_a_1722_, 3);
                            v___x_1746_ = l_Lean_Meta_matchEq_x3f(
                                v_binderType_1736_,
                                v_a_1716_,
                                v_a_1717_,
                                v_a_1718_,
                                v_a_1719_,
                            );
                            if leanh::lean_obj_tag(v___x_1746_) == 0 {
                                v_a_1747_ = leanh::lean_ctor_get(v___x_1746_, 0);
                                leanh::lean_inc(v_a_1747_);
                                leanh::lean_dec_ref_known(v___x_1746_, 1);
                                if leanh::lean_obj_tag(v_a_1747_) == 1 {
                                    v_val_1748_ = leanh::lean_ctor_get(v_a_1747_, 0);
                                    leanh::lean_inc(v_val_1748_);
                                    leanh::lean_dec_ref_known(v_a_1747_, 1);
                                    v_snd_1749_ = leanh::lean_ctor_get(v_val_1748_, 1);
                                    leanh::lean_inc(v_snd_1749_);
                                    leanh::lean_dec(v_val_1748_);
                                    v_snd_1750_ = leanh::lean_ctor_get(v_snd_1749_, 1);
                                    leanh::lean_inc(v_snd_1750_);
                                    leanh::lean_dec(v_snd_1749_);
                                    v___x_1751_ = l_Lean_Meta_mkEqRefl(
                                        v_snd_1750_,
                                        v_a_1716_,
                                        v_a_1717_,
                                        v_a_1718_,
                                        v_a_1719_,
                                    );
                                    if leanh::lean_obj_tag(v___x_1751_) == 0 {
                                        v_a_1752_ = leanh::lean_ctor_get(v___x_1751_, 0);
                                        leanh::lean_inc(v_a_1752_);
                                        leanh::lean_dec_ref_known(v___x_1751_, 1);
                                        v_arg_1739_ = v_a_1752_;
                                        v___y_1740_ = v_a_1716_;
                                        v___y_1741_ = v_a_1717_;
                                        v___y_1742_ = v_a_1718_;
                                        v___y_1743_ = v_a_1719_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v_body_1737_);
                                        leanh::lean_dec_ref(v_binderType_1736_);
                                        leanh::lean_dec(v_binderName_1735_);
                                        leanh::lean_dec(v_i_1714_);
                                        leanh::lean_dec_ref(v_mask_1713_);
                                        leanh::lean_dec_ref(v_args_1712_);
                                        leanh::lean_dec_ref(v_eqs_1711_);
                                        leanh::lean_dec_ref(v_ys_1710_);
                                        leanh::lean_dec_ref(v_k_1709_);
                                        leanh::lean_dec(v_numDiscrEqs_1708_);
                                        leanh::lean_dec_ref(v_altType_1707_);
                                        v_a_1753_ = leanh::lean_ctor_get(v___x_1751_, 0);
                                        v_isSharedCheck_1760_ =
                                            (!leanh::lean_is_exclusive(v___x_1751_)) as u8;
                                        if v_isSharedCheck_1760_ == 0 {
                                            v___x_1755_ = v___x_1751_;
                                            v_isShared_1756_ = v_isSharedCheck_1760_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1753_);
                                            leanh::lean_dec(v___x_1751_);
                                            v___x_1755_ = leanh::lean_box(0);
                                            v_isShared_1756_ = v_isSharedCheck_1760_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1747_);
                                    leanh::lean_inc_ref(v_binderType_1736_);
                                    v___x_1761_ = l_Lean_Meta_matchHEq_x3f(
                                        v_binderType_1736_,
                                        v_a_1716_,
                                        v_a_1717_,
                                        v_a_1718_,
                                        v_a_1719_,
                                    );
                                    if leanh::lean_obj_tag(v___x_1761_) == 0 {
                                        v_a_1762_ = leanh::lean_ctor_get(v___x_1761_, 0);
                                        leanh::lean_inc(v_a_1762_);
                                        leanh::lean_dec_ref_known(v___x_1761_, 1);
                                        if leanh::lean_obj_tag(v_a_1762_) == 1 {
                                            v_val_1763_ = leanh::lean_ctor_get(v_a_1762_, 0);
                                            leanh::lean_inc(v_val_1763_);
                                            leanh::lean_dec_ref_known(v_a_1762_, 1);
                                            v_snd_1764_ =
                                                leanh::lean_ctor_get(v_val_1763_, 1);
                                            leanh::lean_inc(v_snd_1764_);
                                            leanh::lean_dec(v_val_1763_);
                                            v_snd_1765_ =
                                                leanh::lean_ctor_get(v_snd_1764_, 1);
                                            leanh::lean_inc(v_snd_1765_);
                                            leanh::lean_dec(v_snd_1764_);
                                            v_snd_1766_ =
                                                leanh::lean_ctor_get(v_snd_1765_, 1);
                                            leanh::lean_inc(v_snd_1766_);
                                            leanh::lean_dec(v_snd_1765_);
                                            v___x_1767_ = l_Lean_Meta_mkHEqRefl(
                                                v_snd_1766_,
                                                v_a_1716_,
                                                v_a_1717_,
                                                v_a_1718_,
                                                v_a_1719_,
                                            );
                                            if leanh::lean_obj_tag(v___x_1767_) == 0 {
                                                v_a_1768_ =
                                                    leanh::lean_ctor_get(v___x_1767_, 0);
                                                leanh::lean_inc(v_a_1768_);
                                                leanh::lean_dec_ref_known(v___x_1767_, 1);
                                                v_arg_1739_ = v_a_1768_;
                                                v___y_1740_ = v_a_1716_;
                                                v___y_1741_ = v_a_1717_;
                                                v___y_1742_ = v_a_1718_;
                                                v___y_1743_ = v_a_1719_;
                                                state = 3;
                                                continue;
                                            } else {
                                                leanh::lean_dec_ref(v_body_1737_);
                                                leanh::lean_dec_ref(v_binderType_1736_);
                                                leanh::lean_dec(v_binderName_1735_);
                                                leanh::lean_dec(v_i_1714_);
                                                leanh::lean_dec_ref(v_mask_1713_);
                                                leanh::lean_dec_ref(v_args_1712_);
                                                leanh::lean_dec_ref(v_eqs_1711_);
                                                leanh::lean_dec_ref(v_ys_1710_);
                                                leanh::lean_dec_ref(v_k_1709_);
                                                leanh::lean_dec(v_numDiscrEqs_1708_);
                                                leanh::lean_dec_ref(v_altType_1707_);
                                                v_a_1769_ =
                                                    leanh::lean_ctor_get(v___x_1767_, 0);
                                                v_isSharedCheck_1776_ =
                                                    (!leanh::lean_is_exclusive(v___x_1767_))
                                                        as u8;
                                                if v_isSharedCheck_1776_ == 0 {
                                                    v___x_1771_ = v___x_1767_;
                                                    v_isShared_1772_ = v_isSharedCheck_1776_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_1769_);
                                                    leanh::lean_dec(v___x_1767_);
                                                    v___x_1771_ = leanh::lean_box(0);
                                                    v_isShared_1772_ = v_isSharedCheck_1776_;
                                                    state = 6;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_1762_);
                                            v___x_1777_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__1);
                                            leanh::lean_inc_ref(v_altType_1707_);
                                            v___x_1778_ = l_Lean_indentExpr(v_altType_1707_);
                                            v___x_1779_ =
                                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_1779_,
                                                0,
                                                v___x_1777_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_1779_,
                                                1,
                                                v___x_1778_,
                                            );
                                            v___x_1780_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_1779_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
                                            if leanh::lean_obj_tag(v___x_1780_) == 0 {
                                                v_a_1781_ =
                                                    leanh::lean_ctor_get(v___x_1780_, 0);
                                                leanh::lean_inc(v_a_1781_);
                                                leanh::lean_dec_ref_known(v___x_1780_, 1);
                                                v_arg_1739_ = v_a_1781_;
                                                v___y_1740_ = v_a_1716_;
                                                v___y_1741_ = v_a_1717_;
                                                v___y_1742_ = v_a_1718_;
                                                v___y_1743_ = v_a_1719_;
                                                state = 3;
                                                continue;
                                            } else {
                                                leanh::lean_dec_ref(v_body_1737_);
                                                leanh::lean_dec_ref(v_binderType_1736_);
                                                leanh::lean_dec(v_binderName_1735_);
                                                leanh::lean_dec(v_i_1714_);
                                                leanh::lean_dec_ref(v_mask_1713_);
                                                leanh::lean_dec_ref(v_args_1712_);
                                                leanh::lean_dec_ref(v_eqs_1711_);
                                                leanh::lean_dec_ref(v_ys_1710_);
                                                leanh::lean_dec_ref(v_k_1709_);
                                                leanh::lean_dec(v_numDiscrEqs_1708_);
                                                leanh::lean_dec_ref(v_altType_1707_);
                                                v_a_1782_ =
                                                    leanh::lean_ctor_get(v___x_1780_, 0);
                                                v_isSharedCheck_1789_ =
                                                    (!leanh::lean_is_exclusive(v___x_1780_))
                                                        as u8;
                                                if v_isSharedCheck_1789_ == 0 {
                                                    v___x_1784_ = v___x_1780_;
                                                    v_isShared_1785_ = v_isSharedCheck_1789_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_1782_);
                                                    leanh::lean_dec(v___x_1780_);
                                                    v___x_1784_ = leanh::lean_box(0);
                                                    v_isShared_1785_ = v_isSharedCheck_1789_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_body_1737_);
                                        leanh::lean_dec_ref(v_binderType_1736_);
                                        leanh::lean_dec(v_binderName_1735_);
                                        leanh::lean_dec(v_i_1714_);
                                        leanh::lean_dec_ref(v_mask_1713_);
                                        leanh::lean_dec_ref(v_args_1712_);
                                        leanh::lean_dec_ref(v_eqs_1711_);
                                        leanh::lean_dec_ref(v_ys_1710_);
                                        leanh::lean_dec_ref(v_k_1709_);
                                        leanh::lean_dec(v_numDiscrEqs_1708_);
                                        leanh::lean_dec_ref(v_altType_1707_);
                                        v_a_1790_ = leanh::lean_ctor_get(v___x_1761_, 0);
                                        v_isSharedCheck_1797_ =
                                            (!leanh::lean_is_exclusive(v___x_1761_)) as u8;
                                        if v_isSharedCheck_1797_ == 0 {
                                            v___x_1792_ = v___x_1761_;
                                            v_isShared_1793_ = v_isSharedCheck_1797_;
                                            state = 10;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1790_);
                                            leanh::lean_dec(v___x_1761_);
                                            v___x_1792_ = leanh::lean_box(0);
                                            v_isShared_1793_ = v_isSharedCheck_1797_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_1737_);
                                leanh::lean_dec_ref(v_binderType_1736_);
                                leanh::lean_dec(v_binderName_1735_);
                                leanh::lean_dec(v_i_1714_);
                                leanh::lean_dec_ref(v_mask_1713_);
                                leanh::lean_dec_ref(v_args_1712_);
                                leanh::lean_dec_ref(v_eqs_1711_);
                                leanh::lean_dec_ref(v_ys_1710_);
                                leanh::lean_dec_ref(v_k_1709_);
                                leanh::lean_dec(v_numDiscrEqs_1708_);
                                leanh::lean_dec_ref(v_altType_1707_);
                                v_a_1798_ = leanh::lean_ctor_get(v___x_1746_, 0);
                                v_isSharedCheck_1805_ =
                                    (!leanh::lean_is_exclusive(v___x_1746_)) as u8;
                                if v_isSharedCheck_1805_ == 0 {
                                    v___x_1800_ = v___x_1746_;
                                    v_isShared_1801_ = v_isSharedCheck_1805_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1798_);
                                    leanh::lean_dec(v___x_1746_);
                                    v___x_1800_ = leanh::lean_box(0);
                                    v_isShared_1801_ = v_isSharedCheck_1805_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1722_);
                            leanh::lean_dec(v_i_1714_);
                            leanh::lean_dec_ref(v_mask_1713_);
                            leanh::lean_dec_ref(v_args_1712_);
                            leanh::lean_dec_ref(v_eqs_1711_);
                            leanh::lean_dec_ref(v_ys_1710_);
                            leanh::lean_dec_ref(v_k_1709_);
                            v___x_1806_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go___redArg___closed__1);
                            v___x_1807_ = l_Nat_reprFast(v_numDiscrEqs_1708_);
                            v___x_1808_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1808_, 0, v___x_1807_);
                            v___x_1809_ = l_Lean_MessageData_ofFormat(v___x_1808_);
                            v___x_1810_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1810_, 0, v___x_1806_);
                            leanh::lean_ctor_set(v___x_1810_, 1, v___x_1809_);
                            v___x_1811_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3_once), _init_l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___closed__3);
                            v___x_1812_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1812_, 0, v___x_1810_);
                            leanh::lean_ctor_set(v___x_1812_, 1, v___x_1811_);
                            v___x_1813_ = l_Lean_indentExpr(v_altType_1707_);
                            v___x_1814_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1814_, 0, v___x_1812_);
                            leanh::lean_ctor_set(v___x_1814_, 1, v___x_1813_);
                            v___x_1815_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__6___redArg(v___x_1814_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
                            return v___x_1815_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_i_1714_);
                    leanh::lean_dec_ref(v_mask_1713_);
                    leanh::lean_dec_ref(v_args_1712_);
                    leanh::lean_dec_ref(v_eqs_1711_);
                    leanh::lean_dec_ref(v_ys_1710_);
                    leanh::lean_dec_ref(v_k_1709_);
                    leanh::lean_dec(v_numDiscrEqs_1708_);
                    leanh::lean_dec_ref(v_altType_1707_);
                    v_a_1816_ = leanh::lean_ctor_get(v___x_1721_, 0);
                    v_isSharedCheck_1823_ = (!leanh::lean_is_exclusive(v___x_1721_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v___x_1818_ = v___x_1721_;
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1816_);
                        leanh::lean_dec(v___x_1721_);
                        v___x_1818_ = leanh::lean_box(0);
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1730_ == 0 {
                    v___x_1732_ = v___x_1729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1733_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
                    v___x_1732_ = v_reuseFailAlloc_1733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1732_;
            }
            3 => {
                v___f_1744_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 16, 10);
                leanh::lean_closure_set(v___f_1744_, 0, v_body_1737_);
                leanh::lean_closure_set(v___f_1744_, 1, v_eqs_1711_);
                leanh::lean_closure_set(v___f_1744_, 2, v_args_1712_);
                leanh::lean_closure_set(v___f_1744_, 3, v_arg_1739_);
                leanh::lean_closure_set(v___f_1744_, 4, v_mask_1713_);
                leanh::lean_closure_set(v___f_1744_, 5, v_i_1714_);
                leanh::lean_closure_set(v___f_1744_, 6, v_altType_1707_);
                leanh::lean_closure_set(v___f_1744_, 7, v_numDiscrEqs_1708_);
                leanh::lean_closure_set(v___f_1744_, 8, v_k_1709_);
                leanh::lean_closure_set(v___f_1744_, 9, v_ys_1710_);
                v___x_1745_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltVarsTelescope_go_spec__5___redArg(v_binderName_1735_, v_binderType_1736_, v___f_1744_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
                return v___x_1745_;
            }
            4 => {
                if v_isShared_1756_ == 0 {
                    v___x_1758_ = v___x_1755_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
                    v___x_1758_ = v_reuseFailAlloc_1759_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1758_;
            }
            6 => {
                if v_isShared_1772_ == 0 {
                    v___x_1774_ = v___x_1771_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1775_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
                    v___x_1774_ = v_reuseFailAlloc_1775_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1774_;
            }
            8 => {
                if v_isShared_1785_ == 0 {
                    v___x_1787_ = v___x_1784_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1788_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
                    v___x_1787_ = v_reuseFailAlloc_1788_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1787_;
            }
            10 => {
                if v_isShared_1793_ == 0 {
                    v___x_1795_ = v___x_1792_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
                    v___x_1795_ = v_reuseFailAlloc_1796_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1795_;
            }
            12 => {
                if v_isShared_1801_ == 0 {
                    v___x_1803_ = v___x_1800_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
                    v___x_1803_ = v_reuseFailAlloc_1804_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1803_;
            }
            14 => {
                if v_isShared_1819_ == 0 {
                    v___x_1821_ = v___x_1818_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
                    v___x_1821_ = v_reuseFailAlloc_1822_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___lam__0(
    mut v_body_1824_: *mut leanh::LeanObject,
    mut v_eqs_1825_: *mut leanh::LeanObject,
    mut v_args_1826_: *mut leanh::LeanObject,
    mut v_arg_1827_: *mut leanh::LeanObject,
    mut v_mask_1828_: *mut leanh::LeanObject,
    mut v_i_1829_: *mut leanh::LeanObject,
    mut v_altType_1830_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1831_: *mut leanh::LeanObject,
    mut v_k_1832_: *mut leanh::LeanObject,
    mut v_ys_1833_: *mut leanh::LeanObject,
    mut v_eq_1834_: *mut leanh::LeanObject,
    mut v___y_1835_: *mut leanh::LeanObject,
    mut v___y_1836_: *mut leanh::LeanObject,
    mut v___y_1837_: *mut leanh::LeanObject,
    mut v___y_1838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: u8 = 0;
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ = lean_expr_instantiate1(v_body_1824_, v_eq_1834_);
    v___x_1841_ = lean_array_push(v_eqs_1825_, v_eq_1834_);
    v___x_1842_ = lean_array_push(v_args_1826_, v_arg_1827_);
    v___x_1843_ = 0;
    v___x_1844_ = leanh::lean_box((v___x_1843_) as usize);
    v___x_1845_ = lean_array_push(v_mask_1828_, v___x_1844_);
    v___x_1846_ = leanh::lean_unsigned_to_nat(1);
    v___x_1847_ = lean_nat_add(v_i_1829_, v___x_1846_);
    v___x_1848_ =
        l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(
            v_altType_1830_,
            v_numDiscrEqs_1831_,
            v_k_1832_,
            v_ys_1833_,
            v___x_1841_,
            v___x_1842_,
            v___x_1845_,
            v___x_1847_,
            v___x_1840_,
            v___y_1835_,
            v___y_1836_,
            v___y_1837_,
            v___y_1838_,
        );
    return v___x_1848_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg___boxed(
    mut v_altType_1849_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1850_: *mut leanh::LeanObject,
    mut v_k_1851_: *mut leanh::LeanObject,
    mut v_ys_1852_: *mut leanh::LeanObject,
    mut v_eqs_1853_: *mut leanh::LeanObject,
    mut v_args_1854_: *mut leanh::LeanObject,
    mut v_mask_1855_: *mut leanh::LeanObject,
    mut v_i_1856_: *mut leanh::LeanObject,
    mut v_type_1857_: *mut leanh::LeanObject,
    mut v_a_1858_: *mut leanh::LeanObject,
    mut v_a_1859_: *mut leanh::LeanObject,
    mut v_a_1860_: *mut leanh::LeanObject,
    mut v_a_1861_: *mut leanh::LeanObject,
    mut v_a_1862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1863_ =
        l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(
            v_altType_1849_,
            v_numDiscrEqs_1850_,
            v_k_1851_,
            v_ys_1852_,
            v_eqs_1853_,
            v_args_1854_,
            v_mask_1855_,
            v_i_1856_,
            v_type_1857_,
            v_a_1858_,
            v_a_1859_,
            v_a_1860_,
            v_a_1861_,
        );
    leanh::lean_dec(v_a_1861_);
    leanh::lean_dec_ref(v_a_1860_);
    leanh::lean_dec(v_a_1859_);
    leanh::lean_dec_ref(v_a_1858_);
    return v_res_1863_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(
    mut v_00_u03b1_1864_: *mut leanh::LeanObject,
    mut v_altType_1865_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1866_: *mut leanh::LeanObject,
    mut v_k_1867_: *mut leanh::LeanObject,
    mut v_ys_1868_: *mut leanh::LeanObject,
    mut v_eqs_1869_: *mut leanh::LeanObject,
    mut v_args_1870_: *mut leanh::LeanObject,
    mut v_mask_1871_: *mut leanh::LeanObject,
    mut v_i_1872_: *mut leanh::LeanObject,
    mut v_type_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
    mut v_a_1875_: *mut leanh::LeanObject,
    mut v_a_1876_: *mut leanh::LeanObject,
    mut v_a_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ =
        l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(
            v_altType_1865_,
            v_numDiscrEqs_1866_,
            v_k_1867_,
            v_ys_1868_,
            v_eqs_1869_,
            v_args_1870_,
            v_mask_1871_,
            v_i_1872_,
            v_type_1873_,
            v_a_1874_,
            v_a_1875_,
            v_a_1876_,
            v_a_1877_,
        );
    return v___x_1879_;
}
pub unsafe fn l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___boxed(
    mut v_00_u03b1_1880_: *mut leanh::LeanObject,
    mut v_altType_1881_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1882_: *mut leanh::LeanObject,
    mut v_k_1883_: *mut leanh::LeanObject,
    mut v_ys_1884_: *mut leanh::LeanObject,
    mut v_eqs_1885_: *mut leanh::LeanObject,
    mut v_args_1886_: *mut leanh::LeanObject,
    mut v_mask_1887_: *mut leanh::LeanObject,
    mut v_i_1888_: *mut leanh::LeanObject,
    mut v_type_1889_: *mut leanh::LeanObject,
    mut v_a_1890_: *mut leanh::LeanObject,
    mut v_a_1891_: *mut leanh::LeanObject,
    mut v_a_1892_: *mut leanh::LeanObject,
    mut v_a_1893_: *mut leanh::LeanObject,
    mut v_a_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1895_ =
        l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go(
            v_00_u03b1_1880_,
            v_altType_1881_,
            v_numDiscrEqs_1882_,
            v_k_1883_,
            v_ys_1884_,
            v_eqs_1885_,
            v_args_1886_,
            v_mask_1887_,
            v_i_1888_,
            v_type_1889_,
            v_a_1890_,
            v_a_1891_,
            v_a_1892_,
            v_a_1893_,
        );
    leanh::lean_dec(v_a_1893_);
    leanh::lean_dec_ref(v_a_1892_);
    leanh::lean_dec(v_a_1891_);
    leanh::lean_dec_ref(v_a_1890_);
    return v_res_1895_;
}
pub unsafe fn l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(
    mut v_altType_1896_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1897_: *mut leanh::LeanObject,
    mut v_k_1898_: *mut leanh::LeanObject,
    mut v_ys_1899_: *mut leanh::LeanObject,
    mut v_args_1900_: *mut leanh::LeanObject,
    mut v_mask_1901_: *mut leanh::LeanObject,
    mut v_altType_1902_: *mut leanh::LeanObject,
    mut v___y_1903_: *mut leanh::LeanObject,
    mut v___y_1904_: *mut leanh::LeanObject,
    mut v___y_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1908_ = leanh::lean_unsigned_to_nat(0);
    v___x_1909_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg___closed__3;
    v___x_1910_ =
        l___private_Lean_Meta_Match_AltTelescopes_0__Lean_Meta_Match_forallAltTelescope_go___redArg(
            v_altType_1896_,
            v_numDiscrEqs_1897_,
            v_k_1898_,
            v_ys_1899_,
            v___x_1909_,
            v_args_1900_,
            v_mask_1901_,
            v___x_1908_,
            v_altType_1902_,
            v___y_1903_,
            v___y_1904_,
            v___y_1905_,
            v___y_1906_,
        );
    return v___x_1910_;
}
pub unsafe fn l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed(
    mut v_altType_1911_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1912_: *mut leanh::LeanObject,
    mut v_k_1913_: *mut leanh::LeanObject,
    mut v_ys_1914_: *mut leanh::LeanObject,
    mut v_args_1915_: *mut leanh::LeanObject,
    mut v_mask_1916_: *mut leanh::LeanObject,
    mut v_altType_1917_: *mut leanh::LeanObject,
    mut v___y_1918_: *mut leanh::LeanObject,
    mut v___y_1919_: *mut leanh::LeanObject,
    mut v___y_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0(
        v_altType_1911_,
        v_numDiscrEqs_1912_,
        v_k_1913_,
        v_ys_1914_,
        v_args_1915_,
        v_mask_1916_,
        v_altType_1917_,
        v___y_1918_,
        v___y_1919_,
        v___y_1920_,
        v___y_1921_,
    );
    leanh::lean_dec(v___y_1921_);
    leanh::lean_dec_ref(v___y_1920_);
    leanh::lean_dec(v___y_1919_);
    leanh::lean_dec_ref(v___y_1918_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_Meta_Match_forallAltTelescope___redArg(
    mut v_altType_1924_: *mut leanh::LeanObject,
    mut v_altInfo_1925_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1926_: *mut leanh::LeanObject,
    mut v_k_1927_: *mut leanh::LeanObject,
    mut v_a_1928_: *mut leanh::LeanObject,
    mut v_a_1929_: *mut leanh::LeanObject,
    mut v_a_1930_: *mut leanh::LeanObject,
    mut v_a_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_altType_1924_);
    v___f_1933_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Match_forallAltTelescope___redArg___lam__0___boxed as *mut core::ffi::c_void,
        12,
        3,
    );
    leanh::lean_closure_set(v___f_1933_, 0, v_altType_1924_);
    leanh::lean_closure_set(v___f_1933_, 1, v_numDiscrEqs_1926_);
    leanh::lean_closure_set(v___f_1933_, 2, v_k_1927_);
    v___x_1934_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(
        v_altType_1924_,
        v_altInfo_1925_,
        v___f_1933_,
        v_a_1928_,
        v_a_1929_,
        v_a_1930_,
        v_a_1931_,
    );
    return v___x_1934_;
}
pub unsafe fn l_Lean_Meta_Match_forallAltTelescope___redArg___boxed(
    mut v_altType_1935_: *mut leanh::LeanObject,
    mut v_altInfo_1936_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1937_: *mut leanh::LeanObject,
    mut v_k_1938_: *mut leanh::LeanObject,
    mut v_a_1939_: *mut leanh::LeanObject,
    mut v_a_1940_: *mut leanh::LeanObject,
    mut v_a_1941_: *mut leanh::LeanObject,
    mut v_a_1942_: *mut leanh::LeanObject,
    mut v_a_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1944_ = l_Lean_Meta_Match_forallAltTelescope___redArg(
        v_altType_1935_,
        v_altInfo_1936_,
        v_numDiscrEqs_1937_,
        v_k_1938_,
        v_a_1939_,
        v_a_1940_,
        v_a_1941_,
        v_a_1942_,
    );
    leanh::lean_dec(v_a_1942_);
    leanh::lean_dec_ref(v_a_1941_);
    leanh::lean_dec(v_a_1940_);
    leanh::lean_dec_ref(v_a_1939_);
    return v_res_1944_;
}
pub unsafe fn l_Lean_Meta_Match_forallAltTelescope(
    mut v_00_u03b1_1945_: *mut leanh::LeanObject,
    mut v_altType_1946_: *mut leanh::LeanObject,
    mut v_altInfo_1947_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1948_: *mut leanh::LeanObject,
    mut v_k_1949_: *mut leanh::LeanObject,
    mut v_a_1950_: *mut leanh::LeanObject,
    mut v_a_1951_: *mut leanh::LeanObject,
    mut v_a_1952_: *mut leanh::LeanObject,
    mut v_a_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1955_ = l_Lean_Meta_Match_forallAltTelescope___redArg(
        v_altType_1946_,
        v_altInfo_1947_,
        v_numDiscrEqs_1948_,
        v_k_1949_,
        v_a_1950_,
        v_a_1951_,
        v_a_1952_,
        v_a_1953_,
    );
    return v___x_1955_;
}
pub unsafe fn l_Lean_Meta_Match_forallAltTelescope___boxed(
    mut v_00_u03b1_1956_: *mut leanh::LeanObject,
    mut v_altType_1957_: *mut leanh::LeanObject,
    mut v_altInfo_1958_: *mut leanh::LeanObject,
    mut v_numDiscrEqs_1959_: *mut leanh::LeanObject,
    mut v_k_1960_: *mut leanh::LeanObject,
    mut v_a_1961_: *mut leanh::LeanObject,
    mut v_a_1962_: *mut leanh::LeanObject,
    mut v_a_1963_: *mut leanh::LeanObject,
    mut v_a_1964_: *mut leanh::LeanObject,
    mut v_a_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ = l_Lean_Meta_Match_forallAltTelescope(
        v_00_u03b1_1956_,
        v_altType_1957_,
        v_altInfo_1958_,
        v_numDiscrEqs_1959_,
        v_k_1960_,
        v_a_1961_,
        v_a_1962_,
        v_a_1963_,
        v_a_1964_,
    );
    leanh::lean_dec(v_a_1964_);
    leanh::lean_dec_ref(v_a_1963_);
    leanh::lean_dec(v_a_1962_);
    leanh::lean_dec_ref(v_a_1961_);
    return v_res_1966_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_AltTelescopes(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_NamedPatterns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_AltTelescopes(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_AltTelescopes(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_NamedPatterns(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_MatchUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_AltTelescopes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_AltTelescopes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_AltTelescopes(builtin);
}
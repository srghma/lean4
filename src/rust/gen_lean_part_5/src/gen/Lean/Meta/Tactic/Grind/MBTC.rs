// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MBTC
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.CastLike
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_expr_lt, lean_grind_internalize,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_shiftr, lean_nat_sub,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_mix_hash,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hash, l_Lean_Expr_isApp, l_Lean_Expr_sort___override,
    l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkEq;
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfo;
use crate::r#gen::Lean::Meta::Sym::Canon::{
    l_Lean_Meta_Sym_Canon_isSupport, l_Lean_Meta_Sym_canon,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
    l_Lean_Meta_Sym_shareCommon___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::CastLike::{
    initialize_Lean_Meta_Tactic_Grind_CastLike, l_Lean_Meta_Grind_isCastLikeFn,
    runtime_initialize_Lean_Meta_Tactic_Grind_CastLike,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_Goal_getRoot_x3f,
    l_Lean_Meta_Grind_SplitInfo_beq, l_Lean_Meta_Grind_SplitInfo_hash,
    l_Lean_Meta_Grind_SplitInfo_lt, l_Lean_Meta_Grind_addSplitCandidate,
    l_Lean_Meta_Grind_checkMaxCaseSplit___redArg, l_Lean_Meta_Grind_getConfig___redArg,
    l_Lean_Meta_Grind_getGeneration___redArg, l_Lean_Meta_Grind_hasSameType,
    l_Lean_Meta_Grind_isCongrRoot___redArg, l_Lean_Meta_Grind_isKnownCaseSplit___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::ReducibilityAttrs::l_Lean_isImplicitReducibleCore;
use crate::r#gen::Lean::Util::Recognizers::{l_Lean_Expr_isEq, l_Lean_Expr_isHEq};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        95, 95, 103, 114, 105, 110, 100, 95, 109, 97, 105, 110, 95, 97, 114, 103, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value
        ) as *mut leanh::LeanObject,
        4700630907035917417 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [95, 95, 103, 114, 105, 110, 100, 95, 111, 116, 104, 101, 114, 95, 97, 114, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value) as *mut leanh::LeanObject,18094379780977335043 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 98, 116, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1_value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value) as *mut leanh::LeanObject,15448887498159686406 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 64, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value) as *mut leanh::LeanObject,3746410129963432689 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value:
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
static mut l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_mbtc___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mbtc___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mbtc___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mbtc___closed__3_value: leanh::LeanStringObject<72> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 72,
        m_capacity: 72,
        m_length: 71,
        m_data: [
            115, 107, 105, 112, 112, 105, 110, 103, 32, 96, 109, 98, 116, 99, 96, 44, 32, 109, 97,
            120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 115, 112,
            108, 105, 116, 115, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104,
            101, 100, 32, 96, 40, 115, 112, 108, 105, 116, 115, 32, 58, 61, 32, 0,
        ],
    };
static mut l_Lean_Meta_Grind_mbtc___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mbtc___closed__3_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_mbtc___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mbtc___closed__5_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [41, 96, 0],
    };
static mut l_Lean_Meta_Grind_mbtc___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mbtc___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_mbtc___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(
    mut v_x_2478_: *mut leanh::LeanObject,
    mut v_x_2479_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2480_: u8 = 0;
    v___x_2480_ = lean_expr_eqv(v_x_2478_, v_x_2479_);
    return v___x_2480_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed(
    mut v_x_2481_: *mut leanh::LeanObject,
    mut v_x_2482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2483_: u8 = 0;
    let mut v_r_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2483_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(
        v_x_2481_, v_x_2482_,
    );
    leanh::lean_dec_ref(v_x_2482_);
    leanh::lean_dec_ref(v_x_2481_);
    v_r_2484_ = leanh::lean_box((v_res_2483_) as usize);
    return v_r_2484_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(
    mut v_x_2487_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_2488_: u64 = 0;
    let mut v___x_2489_: u64 = 0;
    let mut v___x_2490_: u64 = 0;
    v___x_2488_ = 0u64;
    v___x_2489_ = l_Lean_Expr_hash(v_x_2487_);
    v___x_2490_ = lean_uint64_mix_hash(v___x_2488_, v___x_2489_);
    return v___x_2490_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed(
    mut v_x_2491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2492_: u64 = 0;
    let mut v_r_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2492_ =
        l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_x_2491_);
    leanh::lean_dec_ref(v_x_2491_);
    v_r_2493_ = leanh::lean_box_uint64(v_res_2492_);
    return v_r_2493_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2499_ = leanh::lean_box(0);
    v___x_2500_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1;
    v___x_2501_ = l_Lean_mkConst(v___x_2500_, v___x_2499_);
    return v___x_2501_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark()
-> *mut leanh::LeanObject {
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2502_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2,
    );
    return v___x_2502_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2506_ = leanh::lean_box(0);
    v___x_2507_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1;
    v___x_2508_ = l_Lean_mkConst(v___x_2507_, v___x_2506_);
    return v___x_2508_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark()
-> *mut leanh::LeanObject {
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2509_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2,
    );
    return v___x_2509_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(
    mut v_upperBound_2510_: *mut leanh::LeanObject,
    mut v_i_2511_: *mut leanh::LeanObject,
    mut v_a_2512_: *mut leanh::LeanObject,
    mut v_a_2513_: *mut leanh::LeanObject,
    mut v_b_2514_: *mut leanh::LeanObject,
    mut v___y_2515_: *mut leanh::LeanObject,
    mut v___y_2516_: *mut leanh::LeanObject,
    mut v___y_2517_: *mut leanh::LeanObject,
    mut v___y_2518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: u8 = 0;
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: u8 = 0;
    let mut v_paramInfo_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v_a_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2539_: u8 = 0;
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2543_: u8 = 0;
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2525_ = lean_nat_dec_lt(v_a_2513_, v_upperBound_2510_);
                if v___x_2525_ == 0 {
                    leanh::lean_dec(v_a_2513_);
                    v___x_2526_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2526_, 0, v_b_2514_);
                    return v___x_2526_;
                } else {
                    v___x_2527_ = lean_nat_dec_eq(v_i_2511_, v_a_2513_);
                    if v___x_2527_ == 0 {
                        v_paramInfo_2528_ = leanh::lean_ctor_get(v_a_2512_, 0);
                        v___x_2529_ = lean_array_fget_borrowed(v_b_2514_, v_a_2513_);
                        leanh::lean_inc(v___x_2529_);
                        v___x_2530_ = l_Lean_Meta_Sym_Canon_isSupport(
                            v_paramInfo_2528_,
                            v_a_2513_,
                            v___x_2529_,
                            v___y_2515_,
                            v___y_2516_,
                            v___y_2517_,
                            v___y_2518_,
                        );
                        if leanh::lean_obj_tag(v___x_2530_) == 0 {
                            v_a_2531_ = leanh::lean_ctor_get(v___x_2530_, 0);
                            leanh::lean_inc(v_a_2531_);
                            leanh::lean_dec_ref_known(v___x_2530_, 1);
                            v___x_2535_ = (leanh::lean_unbox(v_a_2531_) as u8);
                            leanh::lean_dec(v_a_2531_);
                            if v___x_2535_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                if v___x_2527_ == 0 {
                                    v_a_2521_ = v_b_2514_;
                                    state = 1;
                                    continue;
                                } else {
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_2514_);
                            leanh::lean_dec(v_a_2513_);
                            v_a_2536_ = leanh::lean_ctor_get(v___x_2530_, 0);
                            v_isSharedCheck_2543_ =
                                (!leanh::lean_is_exclusive(v___x_2530_)) as u8;
                            if v_isSharedCheck_2543_ == 0 {
                                v___x_2538_ = v___x_2530_;
                                v_isShared_2539_ = v_isSharedCheck_2543_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2536_);
                                leanh::lean_dec(v___x_2530_);
                                v___x_2538_ = leanh::lean_box(0);
                                v_isShared_2539_ = v_isSharedCheck_2543_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_2544_ =
                            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark;
                        v___x_2545_ = lean_array_fset(v_b_2514_, v_a_2513_, v___x_2544_);
                        v_a_2521_ = v___x_2545_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2522_ = leanh::lean_unsigned_to_nat(1);
                v___x_2523_ = lean_nat_add(v_a_2513_, v___x_2522_);
                leanh::lean_dec(v_a_2513_);
                v_a_2513_ = v___x_2523_;
                v_b_2514_ = v_a_2521_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2533_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark;
                v___x_2534_ = lean_array_fset(v_b_2514_, v_a_2513_, v___x_2533_);
                v_a_2521_ = v___x_2534_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_2539_ == 0 {
                    v___x_2541_ = v___x_2538_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
                    v___x_2541_ = v_reuseFailAlloc_2542_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg___boxed(
    mut v_upperBound_2546_: *mut leanh::LeanObject,
    mut v_i_2547_: *mut leanh::LeanObject,
    mut v_a_2548_: *mut leanh::LeanObject,
    mut v_a_2549_: *mut leanh::LeanObject,
    mut v_b_2550_: *mut leanh::LeanObject,
    mut v___y_2551_: *mut leanh::LeanObject,
    mut v___y_2552_: *mut leanh::LeanObject,
    mut v___y_2553_: *mut leanh::LeanObject,
    mut v___y_2554_: *mut leanh::LeanObject,
    mut v___y_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_2546_, v_i_2547_, v_a_2548_, v_a_2549_, v_b_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
    leanh::lean_dec(v___y_2554_);
    leanh::lean_dec_ref(v___y_2553_);
    leanh::lean_dec(v___y_2552_);
    leanh::lean_dec_ref(v___y_2551_);
    leanh::lean_dec_ref(v_a_2548_);
    leanh::lean_dec(v_i_2547_);
    leanh::lean_dec(v_upperBound_2546_);
    return v_res_2556_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(
    mut v_i_2557_: *mut leanh::LeanObject,
    mut v_x_2558_: *mut leanh::LeanObject,
    mut v_x_2559_: *mut leanh::LeanObject,
    mut v_x_2560_: *mut leanh::LeanObject,
    mut v___y_2561_: *mut leanh::LeanObject,
    mut v___y_2562_: *mut leanh::LeanObject,
    mut v___y_2563_: *mut leanh::LeanObject,
    mut v___y_2564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2581_: u8 = 0;
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v_a_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2590_: u8 = 0;
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2594_: u8 = 0;
    let mut v_a_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2558_) == 5 {
                    v_fn_2566_ = leanh::lean_ctor_get(v_x_2558_, 0);
                    leanh::lean_inc_ref(v_fn_2566_);
                    v_arg_2567_ = leanh::lean_ctor_get(v_x_2558_, 1);
                    leanh::lean_inc_ref(v_arg_2567_);
                    leanh::lean_dec_ref_known(v_x_2558_, 2);
                    v___x_2568_ = lean_array_set(v_x_2559_, v_x_2560_, v_arg_2567_);
                    v___x_2569_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2570_ = lean_nat_sub(v_x_2560_, v___x_2569_);
                    leanh::lean_dec(v_x_2560_);
                    v_x_2558_ = v_fn_2566_;
                    v_x_2559_ = v___x_2568_;
                    v_x_2560_ = v___x_2570_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_2560_);
                    v___x_2572_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_x_2558_);
                    v___x_2573_ = l_Lean_Meta_getFunInfo(
                        v_x_2558_,
                        v___x_2572_,
                        v___y_2561_,
                        v___y_2562_,
                        v___y_2563_,
                        v___y_2564_,
                    );
                    if leanh::lean_obj_tag(v___x_2573_) == 0 {
                        v_a_2574_ = leanh::lean_ctor_get(v___x_2573_, 0);
                        leanh::lean_inc(v_a_2574_);
                        leanh::lean_dec_ref_known(v___x_2573_, 1);
                        v___x_2575_ = lean_array_get_size(v_x_2559_);
                        v___x_2576_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2577_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v___x_2575_, v_i_2557_, v_a_2574_, v___x_2576_, v_x_2559_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
                        leanh::lean_dec(v_a_2574_);
                        if leanh::lean_obj_tag(v___x_2577_) == 0 {
                            v_a_2578_ = leanh::lean_ctor_get(v___x_2577_, 0);
                            v_isSharedCheck_2586_ =
                                (!leanh::lean_is_exclusive(v___x_2577_)) as u8;
                            if v_isSharedCheck_2586_ == 0 {
                                v___x_2580_ = v___x_2577_;
                                v_isShared_2581_ = v_isSharedCheck_2586_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2578_);
                                leanh::lean_dec(v___x_2577_);
                                v___x_2580_ = leanh::lean_box(0);
                                v_isShared_2581_ = v_isSharedCheck_2586_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_x_2558_);
                            v_a_2587_ = leanh::lean_ctor_get(v___x_2577_, 0);
                            v_isSharedCheck_2594_ =
                                (!leanh::lean_is_exclusive(v___x_2577_)) as u8;
                            if v_isSharedCheck_2594_ == 0 {
                                v___x_2589_ = v___x_2577_;
                                v_isShared_2590_ = v_isSharedCheck_2594_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2587_);
                                leanh::lean_dec(v___x_2577_);
                                v___x_2589_ = leanh::lean_box(0);
                                v_isShared_2590_ = v_isSharedCheck_2594_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_2559_);
                        leanh::lean_dec_ref(v_x_2558_);
                        v_a_2595_ = leanh::lean_ctor_get(v___x_2573_, 0);
                        v_isSharedCheck_2602_ =
                            (!leanh::lean_is_exclusive(v___x_2573_)) as u8;
                        if v_isSharedCheck_2602_ == 0 {
                            v___x_2597_ = v___x_2573_;
                            v_isShared_2598_ = v_isSharedCheck_2602_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2595_);
                            leanh::lean_dec(v___x_2573_);
                            v___x_2597_ = leanh::lean_box(0);
                            v_isShared_2598_ = v_isSharedCheck_2602_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2582_ = l_Lean_mkAppN(v_x_2558_, v_a_2578_);
                leanh::lean_dec(v_a_2578_);
                if v_isShared_2581_ == 0 {
                    leanh::lean_ctor_set(v___x_2580_, 0, v___x_2582_);
                    v___x_2584_ = v___x_2580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
                    v___x_2584_ = v_reuseFailAlloc_2585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2584_;
            }
            3 => {
                if v_isShared_2590_ == 0 {
                    v___x_2592_ = v___x_2589_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
                    v___x_2592_ = v_reuseFailAlloc_2593_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2592_;
            }
            5 => {
                if v_isShared_2598_ == 0 {
                    v___x_2600_ = v___x_2597_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
                    v___x_2600_ = v_reuseFailAlloc_2601_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1___boxed(
    mut v_i_2603_: *mut leanh::LeanObject,
    mut v_x_2604_: *mut leanh::LeanObject,
    mut v_x_2605_: *mut leanh::LeanObject,
    mut v_x_2606_: *mut leanh::LeanObject,
    mut v___y_2607_: *mut leanh::LeanObject,
    mut v___y_2608_: *mut leanh::LeanObject,
    mut v___y_2609_: *mut leanh::LeanObject,
    mut v___y_2610_: *mut leanh::LeanObject,
    mut v___y_2611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2612_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_2603_, v_x_2604_, v_x_2605_, v_x_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
    leanh::lean_dec(v___y_2610_);
    leanh::lean_dec_ref(v___y_2609_);
    leanh::lean_dec(v___y_2608_);
    leanh::lean_dec_ref(v___y_2607_);
    leanh::lean_dec(v_i_2603_);
    return v_res_2612_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = leanh::lean_box(0);
    v_dummy_2614_ = l_Lean_Expr_sort___override(v___x_2613_);
    return v_dummy_2614_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(
    mut v_e_2615_: *mut leanh::LeanObject,
    mut v_i_2616_: *mut leanh::LeanObject,
    mut v_a_2617_: *mut leanh::LeanObject,
    mut v_a_2618_: *mut leanh::LeanObject,
    mut v_a_2619_: *mut leanh::LeanObject,
    mut v_a_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dummy_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dummy_2622_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0,
    );
    v_nargs_2623_ = l_Lean_Expr_getAppNumArgs(v_e_2615_);
    leanh::lean_inc(v_nargs_2623_);
    v___x_2624_ = lean_mk_array(v_nargs_2623_, v_dummy_2622_);
    v___x_2625_ = leanh::lean_unsigned_to_nat(1);
    v___x_2626_ = lean_nat_sub(v_nargs_2623_, v___x_2625_);
    leanh::lean_dec(v_nargs_2623_);
    v___x_2627_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_2616_, v_e_2615_, v___x_2624_, v___x_2626_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
    return v___x_2627_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___boxed(
    mut v_e_2628_: *mut leanh::LeanObject,
    mut v_i_2629_: *mut leanh::LeanObject,
    mut v_a_2630_: *mut leanh::LeanObject,
    mut v_a_2631_: *mut leanh::LeanObject,
    mut v_a_2632_: *mut leanh::LeanObject,
    mut v_a_2633_: *mut leanh::LeanObject,
    mut v_a_2634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2635_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(
        v_e_2628_, v_i_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_,
    );
    leanh::lean_dec(v_a_2633_);
    leanh::lean_dec_ref(v_a_2632_);
    leanh::lean_dec(v_a_2631_);
    leanh::lean_dec_ref(v_a_2630_);
    leanh::lean_dec(v_i_2629_);
    return v_res_2635_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(
    mut v_upperBound_2636_: *mut leanh::LeanObject,
    mut v_i_2637_: *mut leanh::LeanObject,
    mut v_a_2638_: *mut leanh::LeanObject,
    mut v___x_2639_: *mut leanh::LeanObject,
    mut v_inst_2640_: *mut leanh::LeanObject,
    mut v_R_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
    mut v_b_2643_: *mut leanh::LeanObject,
    mut v_c_2644_: *mut leanh::LeanObject,
    mut v___y_2645_: *mut leanh::LeanObject,
    mut v___y_2646_: *mut leanh::LeanObject,
    mut v___y_2647_: *mut leanh::LeanObject,
    mut v___y_2648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2650_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_2636_, v_i_2637_, v_a_2638_, v_a_2642_, v_b_2643_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
    return v___x_2650_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___boxed(
    mut v_upperBound_2651_: *mut leanh::LeanObject,
    mut v_i_2652_: *mut leanh::LeanObject,
    mut v_a_2653_: *mut leanh::LeanObject,
    mut v___x_2654_: *mut leanh::LeanObject,
    mut v_inst_2655_: *mut leanh::LeanObject,
    mut v_R_2656_: *mut leanh::LeanObject,
    mut v_a_2657_: *mut leanh::LeanObject,
    mut v_b_2658_: *mut leanh::LeanObject,
    mut v_c_2659_: *mut leanh::LeanObject,
    mut v___y_2660_: *mut leanh::LeanObject,
    mut v___y_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
    mut v___y_2663_: *mut leanh::LeanObject,
    mut v___y_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(v_upperBound_2651_, v_i_2652_, v_a_2653_, v___x_2654_, v_inst_2655_, v_R_2656_, v_a_2657_, v_b_2658_, v_c_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
    leanh::lean_dec(v___y_2663_);
    leanh::lean_dec_ref(v___y_2662_);
    leanh::lean_dec(v___y_2661_);
    leanh::lean_dec_ref(v___y_2660_);
    leanh::lean_dec(v___x_2654_);
    leanh::lean_dec_ref(v_a_2653_);
    leanh::lean_dec(v_i_2652_);
    leanh::lean_dec(v_upperBound_2651_);
    return v_res_2665_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(
    mut v_a_2666_: *mut leanh::LeanObject,
    mut v_b_2667_: *mut leanh::LeanObject,
    mut v_i_2668_: *mut leanh::LeanObject,
    mut v_a_2669_: *mut leanh::LeanObject,
    mut v_a_2670_: *mut leanh::LeanObject,
    mut v_a_2671_: *mut leanh::LeanObject,
    mut v_a_2672_: *mut leanh::LeanObject,
    mut v_a_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_arg_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_app_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_app_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2691_: u8 = 0;
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_a_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut v_a_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut v_a_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2717_: u8 = 0;
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2721_: u8 = 0;
    let mut v___x_2722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_arg_2676_ = leanh::lean_ctor_get(v_a_2666_, 0);
                leanh::lean_inc_ref(v_arg_2676_);
                v_app_2677_ = leanh::lean_ctor_get(v_a_2666_, 1);
                leanh::lean_inc_ref(v_app_2677_);
                leanh::lean_dec_ref(v_a_2666_);
                v_arg_2678_ = leanh::lean_ctor_get(v_b_2667_, 0);
                leanh::lean_inc_ref(v_arg_2678_);
                v_app_2679_ = leanh::lean_ctor_get(v_b_2667_, 1);
                leanh::lean_inc_ref(v_app_2679_);
                leanh::lean_dec_ref(v_b_2667_);
                v___x_2722_ = lean_expr_lt(v_arg_2676_, v_arg_2678_);
                if v___x_2722_ == 0 {
                    v_fst_2681_ = v_arg_2678_;
                    v_snd_2682_ = v_arg_2676_;
                    state = 1;
                    continue;
                } else {
                    v_fst_2681_ = v_arg_2676_;
                    v_snd_2682_ = v_arg_2678_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2683_ = l_Lean_Meta_mkEq(
                    v_fst_2681_,
                    v_snd_2682_,
                    v_a_2671_,
                    v_a_2672_,
                    v_a_2673_,
                    v_a_2674_,
                );
                if leanh::lean_obj_tag(v___x_2683_) == 0 {
                    v_a_2684_ = leanh::lean_ctor_get(v___x_2683_, 0);
                    leanh::lean_inc(v_a_2684_);
                    leanh::lean_dec_ref_known(v___x_2683_, 1);
                    v___x_2685_ = l_Lean_Meta_Sym_canon(
                        v_a_2684_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_,
                    );
                    if leanh::lean_obj_tag(v___x_2685_) == 0 {
                        v_a_2686_ = leanh::lean_ctor_get(v___x_2685_, 0);
                        leanh::lean_inc(v_a_2686_);
                        leanh::lean_dec_ref_known(v___x_2685_, 1);
                        v___x_2687_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2686_, v_a_2670_);
                        if leanh::lean_obj_tag(v___x_2687_) == 0 {
                            v_a_2688_ = leanh::lean_ctor_get(v___x_2687_, 0);
                            v_isSharedCheck_2697_ =
                                (!leanh::lean_is_exclusive(v___x_2687_)) as u8;
                            if v_isSharedCheck_2697_ == 0 {
                                v___x_2690_ = v___x_2687_;
                                v_isShared_2691_ = v_isSharedCheck_2697_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2688_);
                                leanh::lean_dec(v___x_2687_);
                                v___x_2690_ = leanh::lean_box(0);
                                v_isShared_2691_ = v_isSharedCheck_2697_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_app_2679_);
                            leanh::lean_dec_ref(v_app_2677_);
                            leanh::lean_dec(v_i_2668_);
                            v_a_2698_ = leanh::lean_ctor_get(v___x_2687_, 0);
                            v_isSharedCheck_2705_ =
                                (!leanh::lean_is_exclusive(v___x_2687_)) as u8;
                            if v_isSharedCheck_2705_ == 0 {
                                v___x_2700_ = v___x_2687_;
                                v_isShared_2701_ = v_isSharedCheck_2705_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2698_);
                                leanh::lean_dec(v___x_2687_);
                                v___x_2700_ = leanh::lean_box(0);
                                v_isShared_2701_ = v_isSharedCheck_2705_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_app_2679_);
                        leanh::lean_dec_ref(v_app_2677_);
                        leanh::lean_dec(v_i_2668_);
                        v_a_2706_ = leanh::lean_ctor_get(v___x_2685_, 0);
                        v_isSharedCheck_2713_ =
                            (!leanh::lean_is_exclusive(v___x_2685_)) as u8;
                        if v_isSharedCheck_2713_ == 0 {
                            v___x_2708_ = v___x_2685_;
                            v_isShared_2709_ = v_isSharedCheck_2713_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2706_);
                            leanh::lean_dec(v___x_2685_);
                            v___x_2708_ = leanh::lean_box(0);
                            v_isShared_2709_ = v_isSharedCheck_2713_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_app_2679_);
                    leanh::lean_dec_ref(v_app_2677_);
                    leanh::lean_dec(v_i_2668_);
                    v_a_2714_ = leanh::lean_ctor_get(v___x_2683_, 0);
                    v_isSharedCheck_2721_ = (!leanh::lean_is_exclusive(v___x_2683_)) as u8;
                    if v_isSharedCheck_2721_ == 0 {
                        v___x_2716_ = v___x_2683_;
                        v_isShared_2717_ = v_isSharedCheck_2721_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2714_);
                        leanh::lean_dec(v___x_2683_);
                        v___x_2716_ = leanh::lean_box(0);
                        v_isShared_2717_ = v_isSharedCheck_2721_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_i_2668_);
                leanh::lean_inc_ref(v_app_2679_);
                leanh::lean_inc_ref(v_app_2677_);
                v___x_2692_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2692_, 0, v_app_2677_);
                leanh::lean_ctor_set(v___x_2692_, 1, v_app_2679_);
                leanh::lean_ctor_set(v___x_2692_, 2, v_i_2668_);
                v___x_2693_ = leanh::lean_alloc_ctor(2, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2693_, 0, v_app_2677_);
                leanh::lean_ctor_set(v___x_2693_, 1, v_app_2679_);
                leanh::lean_ctor_set(v___x_2693_, 2, v_i_2668_);
                leanh::lean_ctor_set(v___x_2693_, 3, v_a_2688_);
                leanh::lean_ctor_set(v___x_2693_, 4, v___x_2692_);
                if v_isShared_2691_ == 0 {
                    leanh::lean_ctor_set(v___x_2690_, 0, v___x_2693_);
                    v___x_2695_ = v___x_2690_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2696_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
                    v___x_2695_ = v_reuseFailAlloc_2696_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2695_;
            }
            4 => {
                if v_isShared_2701_ == 0 {
                    v___x_2703_ = v___x_2700_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
                    v___x_2703_ = v_reuseFailAlloc_2704_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2703_;
            }
            6 => {
                if v_isShared_2709_ == 0 {
                    v___x_2711_ = v___x_2708_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
                    v___x_2711_ = v_reuseFailAlloc_2712_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2711_;
            }
            8 => {
                if v_isShared_2717_ == 0 {
                    v___x_2719_ = v___x_2716_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2720_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
                    v___x_2719_ = v_reuseFailAlloc_2720_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg___boxed(
    mut v_a_2723_: *mut leanh::LeanObject,
    mut v_b_2724_: *mut leanh::LeanObject,
    mut v_i_2725_: *mut leanh::LeanObject,
    mut v_a_2726_: *mut leanh::LeanObject,
    mut v_a_2727_: *mut leanh::LeanObject,
    mut v_a_2728_: *mut leanh::LeanObject,
    mut v_a_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
    mut v_a_2731_: *mut leanh::LeanObject,
    mut v_a_2732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2733_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(
        v_a_2723_, v_b_2724_, v_i_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_,
        v_a_2731_,
    );
    leanh::lean_dec(v_a_2731_);
    leanh::lean_dec_ref(v_a_2730_);
    leanh::lean_dec(v_a_2729_);
    leanh::lean_dec_ref(v_a_2728_);
    leanh::lean_dec(v_a_2727_);
    leanh::lean_dec_ref(v_a_2726_);
    return v_res_2733_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(
    mut v_a_2734_: *mut leanh::LeanObject,
    mut v_b_2735_: *mut leanh::LeanObject,
    mut v_i_2736_: *mut leanh::LeanObject,
    mut v_a_2737_: *mut leanh::LeanObject,
    mut v_a_2738_: *mut leanh::LeanObject,
    mut v_a_2739_: *mut leanh::LeanObject,
    mut v_a_2740_: *mut leanh::LeanObject,
    mut v_a_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
    mut v_a_2744_: *mut leanh::LeanObject,
    mut v_a_2745_: *mut leanh::LeanObject,
    mut v_a_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(
        v_a_2734_, v_b_2735_, v_i_2736_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_,
        v_a_2746_,
    );
    return v___x_2748_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___boxed(
    mut v_a_2749_: *mut leanh::LeanObject,
    mut v_b_2750_: *mut leanh::LeanObject,
    mut v_i_2751_: *mut leanh::LeanObject,
    mut v_a_2752_: *mut leanh::LeanObject,
    mut v_a_2753_: *mut leanh::LeanObject,
    mut v_a_2754_: *mut leanh::LeanObject,
    mut v_a_2755_: *mut leanh::LeanObject,
    mut v_a_2756_: *mut leanh::LeanObject,
    mut v_a_2757_: *mut leanh::LeanObject,
    mut v_a_2758_: *mut leanh::LeanObject,
    mut v_a_2759_: *mut leanh::LeanObject,
    mut v_a_2760_: *mut leanh::LeanObject,
    mut v_a_2761_: *mut leanh::LeanObject,
    mut v_a_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2763_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(
        v_a_2749_, v_b_2750_, v_i_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_,
        v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_,
    );
    leanh::lean_dec(v_a_2761_);
    leanh::lean_dec_ref(v_a_2760_);
    leanh::lean_dec(v_a_2759_);
    leanh::lean_dec_ref(v_a_2758_);
    leanh::lean_dec(v_a_2757_);
    leanh::lean_dec_ref(v_a_2756_);
    leanh::lean_dec(v_a_2755_);
    leanh::lean_dec_ref(v_a_2754_);
    leanh::lean_dec(v_a_2753_);
    leanh::lean_dec(v_a_2752_);
    return v_res_2763_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(
    mut v_declName_2764_: *mut leanh::LeanObject,
    mut v___y_2765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2767_ = lean_st_ref_get(v___y_2765_);
    v_env_2768_ = leanh::lean_ctor_get(v___x_2767_, 0);
    leanh::lean_inc_ref(v_env_2768_);
    leanh::lean_dec(v___x_2767_);
    v___x_2769_ = l_Lean_isImplicitReducibleCore(v_env_2768_, v_declName_2764_);
    v___x_2770_ = leanh::lean_box((v___x_2769_) as usize);
    v___x_2771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2771_, 0, v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg___boxed(
    mut v_declName_2772_: *mut leanh::LeanObject,
    mut v___y_2773_: *mut leanh::LeanObject,
    mut v___y_2774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2775_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_2772_, v___y_2773_);
    leanh::lean_dec(v___y_2773_);
    return v_res_2775_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(
    mut v_declName_2776_: *mut leanh::LeanObject,
    mut v___y_2777_: *mut leanh::LeanObject,
    mut v___y_2778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2780_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_2776_, v___y_2778_);
    return v___x_2780_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___boxed(
    mut v_declName_2781_: *mut leanh::LeanObject,
    mut v___y_2782_: *mut leanh::LeanObject,
    mut v___y_2783_: *mut leanh::LeanObject,
    mut v___y_2784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2785_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(v_declName_2781_, v___y_2782_, v___y_2783_);
    leanh::lean_dec(v___y_2783_);
    leanh::lean_dec_ref(v___y_2782_);
    return v_res_2785_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(
    mut v_f_2786_: *mut leanh::LeanObject,
    mut v_a_2787_: *mut leanh::LeanObject,
    mut v_a_2788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_f_2786_) == 4 {
        let mut v_declName_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_declName_2790_ = leanh::lean_ctor_get(v_f_2786_, 0);
        leanh::lean_inc(v_declName_2790_);
        leanh::lean_dec_ref_known(v_f_2786_, 2);
        v___x_2791_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_2790_, v_a_2788_);
        return v___x_2791_;
    } else {
        let mut v___x_2792_: u8 = 0;
        let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_2786_);
        v___x_2792_ = 0;
        v___x_2793_ = leanh::lean_box((v___x_2792_) as usize);
        v___x_2794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2794_, 0, v___x_2793_);
        return v___x_2794_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___boxed(
    mut v_f_2795_: *mut leanh::LeanObject,
    mut v_a_2796_: *mut leanh::LeanObject,
    mut v_a_2797_: *mut leanh::LeanObject,
    mut v_a_2798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2799_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(
        v_f_2795_, v_a_2796_, v_a_2797_,
    );
    leanh::lean_dec(v_a_2797_);
    leanh::lean_dec_ref(v_a_2796_);
    return v_res_2799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(
    mut v_as_2800_: *mut leanh::LeanObject,
    mut v_sz_2801_: usize,
    mut v_i_2802_: usize,
    mut v_b_2803_: *mut leanh::LeanObject,
    mut v___y_2804_: *mut leanh::LeanObject,
    mut v___y_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
    mut v___y_2808_: *mut leanh::LeanObject,
    mut v___y_2809_: *mut leanh::LeanObject,
    mut v___y_2810_: *mut leanh::LeanObject,
    mut v___y_2811_: *mut leanh::LeanObject,
    mut v___y_2812_: *mut leanh::LeanObject,
    mut v___y_2813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: usize = 0;
    let mut v___x_2821_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2815_ = lean_usize_dec_lt(v_i_2802_, v_sz_2801_);
                if v___x_2815_ == 0 {
                    v___x_2816_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2816_, 0, v_b_2803_);
                    return v___x_2816_;
                } else {
                    v_a_2817_ = lean_array_uget_borrowed(v_as_2800_, v_i_2802_);
                    leanh::lean_inc(v_a_2817_);
                    v___x_2818_ = l_Lean_Meta_Grind_addSplitCandidate(
                        v_a_2817_,
                        v___y_2804_,
                        v___y_2805_,
                        v___y_2806_,
                        v___y_2807_,
                        v___y_2808_,
                        v___y_2809_,
                        v___y_2810_,
                        v___y_2811_,
                        v___y_2812_,
                        v___y_2813_,
                    );
                    if leanh::lean_obj_tag(v___x_2818_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2818_, 1);
                        v___x_2819_ = leanh::lean_box(0);
                        v___x_2820_ = 1usize;
                        v___x_2821_ = lean_usize_add(v_i_2802_, v___x_2820_);
                        v_i_2802_ = v___x_2821_;
                        v_b_2803_ = v___x_2819_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2818_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9___boxed(
    mut v_as_2823_: *mut leanh::LeanObject,
    mut v_sz_2824_: *mut leanh::LeanObject,
    mut v_i_2825_: *mut leanh::LeanObject,
    mut v_b_2826_: *mut leanh::LeanObject,
    mut v___y_2827_: *mut leanh::LeanObject,
    mut v___y_2828_: *mut leanh::LeanObject,
    mut v___y_2829_: *mut leanh::LeanObject,
    mut v___y_2830_: *mut leanh::LeanObject,
    mut v___y_2831_: *mut leanh::LeanObject,
    mut v___y_2832_: *mut leanh::LeanObject,
    mut v___y_2833_: *mut leanh::LeanObject,
    mut v___y_2834_: *mut leanh::LeanObject,
    mut v___y_2835_: *mut leanh::LeanObject,
    mut v___y_2836_: *mut leanh::LeanObject,
    mut v___y_2837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2838_: usize = 0;
    let mut v_i_boxed_2839_: usize = 0;
    let mut v_res_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2838_ = leanh::lean_unbox_usize(v_sz_2824_);
    leanh::lean_dec(v_sz_2824_);
    v_i_boxed_2839_ = leanh::lean_unbox_usize(v_i_2825_);
    leanh::lean_dec(v_i_2825_);
    v_res_2840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_as_2823_, v_sz_boxed_2838_, v_i_boxed_2839_, v_b_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
    leanh::lean_dec(v___y_2836_);
    leanh::lean_dec_ref(v___y_2835_);
    leanh::lean_dec(v___y_2834_);
    leanh::lean_dec_ref(v___y_2833_);
    leanh::lean_dec(v___y_2832_);
    leanh::lean_dec_ref(v___y_2831_);
    leanh::lean_dec(v___y_2830_);
    leanh::lean_dec_ref(v___y_2829_);
    leanh::lean_dec(v___y_2828_);
    leanh::lean_dec(v___y_2827_);
    leanh::lean_dec_ref(v_as_2823_);
    return v_res_2840_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(
    mut v_x_2841_: *mut leanh::LeanObject,
    mut v_x_2842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2842_) == 0 {
                    return v_x_2841_;
                } else {
                    v_key_2843_ = leanh::lean_ctor_get(v_x_2842_, 0);
                    leanh::lean_inc(v_key_2843_);
                    v_tail_2844_ = leanh::lean_ctor_get(v_x_2842_, 2);
                    leanh::lean_inc(v_tail_2844_);
                    leanh::lean_dec_ref_known(v_x_2842_, 3);
                    v___x_2845_ = lean_array_push(v_x_2841_, v_key_2843_);
                    v_x_2841_ = v___x_2845_;
                    v_x_2842_ = v_tail_2844_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(
    mut v_as_2847_: *mut leanh::LeanObject,
    mut v_i_2848_: usize,
    mut v_stop_2849_: usize,
    mut v_b_2850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: usize = 0;
    let mut v___x_2855_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2851_ = lean_usize_dec_eq(v_i_2848_, v_stop_2849_);
                if v___x_2851_ == 0 {
                    v___x_2852_ = lean_array_uget_borrowed(v_as_2847_, v_i_2848_);
                    leanh::lean_inc(v___x_2852_);
                    v___x_2853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(v_b_2850_, v___x_2852_);
                    v___x_2854_ = 1usize;
                    v___x_2855_ = lean_usize_add(v_i_2848_, v___x_2854_);
                    v_i_2848_ = v___x_2855_;
                    v_b_2850_ = v___x_2853_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2850_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12___boxed(
    mut v_as_2857_: *mut leanh::LeanObject,
    mut v_i_2858_: *mut leanh::LeanObject,
    mut v_stop_2859_: *mut leanh::LeanObject,
    mut v_b_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2861_: usize = 0;
    let mut v_stop_boxed_2862_: usize = 0;
    let mut v_res_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2861_ = leanh::lean_unbox_usize(v_i_2858_);
    leanh::lean_dec(v_i_2858_);
    v_stop_boxed_2862_ = leanh::lean_unbox_usize(v_stop_2859_);
    leanh::lean_dec(v_stop_2859_);
    v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_as_2857_, v_i_boxed_2861_, v_stop_boxed_2862_, v_b_2860_);
    leanh::lean_dec_ref(v_as_2857_);
    return v_res_2863_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(
    mut v_hi_2864_: *mut leanh::LeanObject,
    mut v_pivot_2865_: *mut leanh::LeanObject,
    mut v_as_2866_: *mut leanh::LeanObject,
    mut v_i_2867_: *mut leanh::LeanObject,
    mut v_k_2868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2869_: u8 = 0;
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2869_ = lean_nat_dec_lt(v_k_2868_, v_hi_2864_);
                if v___x_2869_ == 0 {
                    leanh::lean_dec(v_k_2868_);
                    v___x_2870_ = lean_array_fswap(v_as_2866_, v_i_2867_, v_hi_2864_);
                    v___x_2871_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2871_, 0, v_i_2867_);
                    leanh::lean_ctor_set(v___x_2871_, 1, v___x_2870_);
                    return v___x_2871_;
                } else {
                    v___x_2872_ = lean_array_fget_borrowed(v_as_2866_, v_k_2868_);
                    v___x_2873_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2872_, v_pivot_2865_);
                    if v___x_2873_ == 0 {
                        v___x_2874_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2875_ = lean_nat_add(v_k_2868_, v___x_2874_);
                        leanh::lean_dec(v_k_2868_);
                        v_k_2868_ = v___x_2875_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2877_ = lean_array_fswap(v_as_2866_, v_i_2867_, v_k_2868_);
                        v___x_2878_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2879_ = lean_nat_add(v_i_2867_, v___x_2878_);
                        leanh::lean_dec(v_i_2867_);
                        v___x_2880_ = lean_nat_add(v_k_2868_, v___x_2878_);
                        leanh::lean_dec(v_k_2868_);
                        v_as_2866_ = v___x_2877_;
                        v_i_2867_ = v___x_2879_;
                        v_k_2868_ = v___x_2880_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg___boxed(
    mut v_hi_2882_: *mut leanh::LeanObject,
    mut v_pivot_2883_: *mut leanh::LeanObject,
    mut v_as_2884_: *mut leanh::LeanObject,
    mut v_i_2885_: *mut leanh::LeanObject,
    mut v_k_2886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2887_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2882_, v_pivot_2883_, v_as_2884_, v_i_2885_, v_k_2886_);
    leanh::lean_dec_ref(v_pivot_2883_);
    leanh::lean_dec(v_hi_2882_);
    return v_res_2887_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(
    mut v_n_2888_: *mut leanh::LeanObject,
    mut v_as_2889_: *mut leanh::LeanObject,
    mut v_lo_2890_: *mut leanh::LeanObject,
    mut v_hi_2891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: u8 = 0;
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2903_ = lean_nat_dec_lt(v_lo_2890_, v_hi_2891_);
                if v___x_2903_ == 0 {
                    leanh::lean_dec(v_lo_2890_);
                    return v_as_2889_;
                } else {
                    v___x_2904_ = lean_nat_add(v_lo_2890_, v_hi_2891_);
                    v___x_2905_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2906_ = lean_nat_shiftr(v___x_2904_, v___x_2905_);
                    leanh::lean_dec(v___x_2904_);
                    v___x_2919_ = lean_array_fget_borrowed(v_as_2889_, v_mid_2906_);
                    v___x_2920_ = lean_array_fget_borrowed(v_as_2889_, v_lo_2890_);
                    v___x_2921_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2919_, v___x_2920_);
                    if v___x_2921_ == 0 {
                        v___y_2914_ = v_as_2889_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2922_ = lean_array_fswap(v_as_2889_, v_lo_2890_, v_mid_2906_);
                        v___y_2914_ = v___x_2922_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2894_ = lean_array_fget(v___y_2893_, v_hi_2891_);
                leanh::lean_inc_n(v_lo_2890_, 2);
                v___x_2895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2891_, v_pivot_2894_, v___y_2893_, v_lo_2890_, v_lo_2890_);
                leanh::lean_dec(v_pivot_2894_);
                v_fst_2896_ = leanh::lean_ctor_get(v___x_2895_, 0);
                leanh::lean_inc(v_fst_2896_);
                v_snd_2897_ = leanh::lean_ctor_get(v___x_2895_, 1);
                leanh::lean_inc(v_snd_2897_);
                leanh::lean_dec_ref(v___x_2895_);
                v___x_2898_ = lean_nat_dec_le(v_hi_2891_, v_fst_2896_);
                if v___x_2898_ == 0 {
                    v___x_2899_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2888_, v_snd_2897_, v_lo_2890_, v_fst_2896_);
                    v___x_2900_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2901_ = lean_nat_add(v_fst_2896_, v___x_2900_);
                    leanh::lean_dec(v_fst_2896_);
                    v_as_2889_ = v___x_2899_;
                    v_lo_2890_ = v___x_2901_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2896_);
                    leanh::lean_dec(v_lo_2890_);
                    return v_snd_2897_;
                }
            }
            2 => {
                v___x_2909_ = lean_array_fget_borrowed(v___y_2908_, v_mid_2906_);
                v___x_2910_ = lean_array_fget_borrowed(v___y_2908_, v_hi_2891_);
                v___x_2911_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2909_, v___x_2910_);
                if v___x_2911_ == 0 {
                    leanh::lean_dec(v_mid_2906_);
                    v___y_2893_ = v___y_2908_;
                    state = 1;
                    continue;
                } else {
                    v___x_2912_ = lean_array_fswap(v___y_2908_, v_mid_2906_, v_hi_2891_);
                    leanh::lean_dec(v_mid_2906_);
                    v___y_2893_ = v___x_2912_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2915_ = lean_array_fget_borrowed(v___y_2914_, v_hi_2891_);
                v___x_2916_ = lean_array_fget_borrowed(v___y_2914_, v_lo_2890_);
                v___x_2917_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2915_, v___x_2916_);
                if v___x_2917_ == 0 {
                    v___y_2908_ = v___y_2914_;
                    state = 2;
                    continue;
                } else {
                    v___x_2918_ = lean_array_fswap(v___y_2914_, v_lo_2890_, v_hi_2891_);
                    v___y_2908_ = v___x_2918_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg___boxed(
    mut v_n_2923_: *mut leanh::LeanObject,
    mut v_as_2924_: *mut leanh::LeanObject,
    mut v_lo_2925_: *mut leanh::LeanObject,
    mut v_hi_2926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2927_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2923_, v_as_2924_, v_lo_2925_, v_hi_2926_);
    leanh::lean_dec(v_hi_2926_);
    leanh::lean_dec(v_n_2923_);
    return v_res_2927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(
    mut v_a_2928_: *mut leanh::LeanObject,
    mut v_x_2929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: u8 = 0;
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2929_) == 0 {
                    v___x_2930_ = leanh::lean_box(0);
                    return v___x_2930_;
                } else {
                    v_key_2931_ = leanh::lean_ctor_get(v_x_2929_, 0);
                    v_value_2932_ = leanh::lean_ctor_get(v_x_2929_, 1);
                    v_tail_2933_ = leanh::lean_ctor_get(v_x_2929_, 2);
                    v___x_2934_ = lean_expr_eqv(v_key_2931_, v_a_2928_);
                    if v___x_2934_ == 0 {
                        v_x_2929_ = v_tail_2933_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_2932_);
                        v___x_2936_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2936_, 0, v_value_2932_);
                        return v___x_2936_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg___boxed(
    mut v_a_2937_: *mut leanh::LeanObject,
    mut v_x_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2939_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2937_, v_x_2938_);
    leanh::lean_dec(v_x_2938_);
    leanh::lean_dec_ref(v_a_2937_);
    return v_res_2939_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(
    mut v_m_2940_: *mut leanh::LeanObject,
    mut v_a_2941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: u64 = 0;
    let mut v___x_2945_: u64 = 0;
    let mut v___x_2946_: u64 = 0;
    let mut v_fold_2947_: u64 = 0;
    let mut v___x_2948_: u64 = 0;
    let mut v___x_2949_: u64 = 0;
    let mut v___x_2950_: u64 = 0;
    let mut v___x_2951_: usize = 0;
    let mut v___x_2952_: usize = 0;
    let mut v___x_2953_: usize = 0;
    let mut v___x_2954_: usize = 0;
    let mut v___x_2955_: usize = 0;
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2942_ = leanh::lean_ctor_get(v_m_2940_, 1);
    v___x_2943_ = lean_array_get_size(v_buckets_2942_);
    v___x_2944_ =
        l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_a_2941_);
    v___x_2945_ = 32u64;
    v___x_2946_ = lean_uint64_shift_right(v___x_2944_, v___x_2945_);
    v_fold_2947_ = lean_uint64_xor(v___x_2944_, v___x_2946_);
    v___x_2948_ = 16u64;
    v___x_2949_ = lean_uint64_shift_right(v_fold_2947_, v___x_2948_);
    v___x_2950_ = lean_uint64_xor(v_fold_2947_, v___x_2949_);
    v___x_2951_ = lean_uint64_to_usize(v___x_2950_);
    v___x_2952_ = lean_usize_of_nat(v___x_2943_);
    v___x_2953_ = 1usize;
    v___x_2954_ = lean_usize_sub(v___x_2952_, v___x_2953_);
    v___x_2955_ = lean_usize_land(v___x_2951_, v___x_2954_);
    v___x_2956_ = lean_array_uget_borrowed(v_buckets_2942_, v___x_2955_);
    v___x_2957_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2941_, v___x_2956_);
    return v___x_2957_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg___boxed(
    mut v_m_2958_: *mut leanh::LeanObject,
    mut v_a_2959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2958_, v_a_2959_);
    leanh::lean_dec_ref(v_a_2959_);
    leanh::lean_dec_ref(v_m_2958_);
    return v_res_2960_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(
    mut v_msgData_2961_: *mut leanh::LeanObject,
    mut v___y_2962_: *mut leanh::LeanObject,
    mut v___y_2963_: *mut leanh::LeanObject,
    mut v___y_2964_: *mut leanh::LeanObject,
    mut v___y_2965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2967_ = lean_st_ref_get(v___y_2965_);
    v_env_2968_ = leanh::lean_ctor_get(v___x_2967_, 0);
    leanh::lean_inc_ref(v_env_2968_);
    leanh::lean_dec(v___x_2967_);
    v___x_2969_ = lean_st_ref_get(v___y_2963_);
    v_mctx_2970_ = leanh::lean_ctor_get(v___x_2969_, 0);
    leanh::lean_inc_ref(v_mctx_2970_);
    leanh::lean_dec(v___x_2969_);
    v_lctx_2971_ = leanh::lean_ctor_get(v___y_2962_, 2);
    v_options_2972_ = leanh::lean_ctor_get(v___y_2964_, 2);
    leanh::lean_inc_ref(v_options_2972_);
    leanh::lean_inc_ref(v_lctx_2971_);
    v___x_2973_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2973_, 0, v_env_2968_);
    leanh::lean_ctor_set(v___x_2973_, 1, v_mctx_2970_);
    leanh::lean_ctor_set(v___x_2973_, 2, v_lctx_2971_);
    leanh::lean_ctor_set(v___x_2973_, 3, v_options_2972_);
    v___x_2974_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2974_, 0, v___x_2973_);
    leanh::lean_ctor_set(v___x_2974_, 1, v_msgData_2961_);
    v___x_2975_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2975_, 0, v___x_2974_);
    return v___x_2975_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0___boxed(
    mut v_msgData_2976_: *mut leanh::LeanObject,
    mut v___y_2977_: *mut leanh::LeanObject,
    mut v___y_2978_: *mut leanh::LeanObject,
    mut v___y_2979_: *mut leanh::LeanObject,
    mut v___y_2980_: *mut leanh::LeanObject,
    mut v___y_2981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msgData_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
    leanh::lean_dec(v___y_2980_);
    leanh::lean_dec_ref(v___y_2979_);
    leanh::lean_dec(v___y_2978_);
    leanh::lean_dec_ref(v___y_2977_);
    return v_res_2982_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: f64 = 0.0;
    v___x_2983_ = leanh::lean_unsigned_to_nat(0);
    v___x_2984_ = lean_float_of_nat(v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(
    mut v_cls_2988_: *mut leanh::LeanObject,
    mut v_msg_2989_: *mut leanh::LeanObject,
    mut v___y_2990_: *mut leanh::LeanObject,
    mut v___y_2991_: *mut leanh::LeanObject,
    mut v___y_2992_: *mut leanh::LeanObject,
    mut v___y_2993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v_tid_3014_: u64 = 0;
    let mut v_traces_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: f64 = 0.0;
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v_isSharedCheck_3040_: u8 = 0;
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2995_ = leanh::lean_ctor_get(v___y_2992_, 5);
                v___x_2996_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msg_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
                v_a_2997_ = leanh::lean_ctor_get(v___x_2996_, 0);
                v_isSharedCheck_3041_ = (!leanh::lean_is_exclusive(v___x_2996_)) as u8;
                if v_isSharedCheck_3041_ == 0 {
                    v___x_2999_ = v___x_2996_;
                    v_isShared_3000_ = v_isSharedCheck_3041_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2997_);
                    leanh::lean_dec(v___x_2996_);
                    v___x_2999_ = leanh::lean_box(0);
                    v_isShared_3000_ = v_isSharedCheck_3041_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3001_ = lean_st_ref_take(v___y_2993_);
                v_traceState_3002_ = leanh::lean_ctor_get(v___x_3001_, 4);
                v_env_3003_ = leanh::lean_ctor_get(v___x_3001_, 0);
                v_nextMacroScope_3004_ = leanh::lean_ctor_get(v___x_3001_, 1);
                v_ngen_3005_ = leanh::lean_ctor_get(v___x_3001_, 2);
                v_auxDeclNGen_3006_ = leanh::lean_ctor_get(v___x_3001_, 3);
                v_cache_3007_ = leanh::lean_ctor_get(v___x_3001_, 5);
                v_messages_3008_ = leanh::lean_ctor_get(v___x_3001_, 6);
                v_infoState_3009_ = leanh::lean_ctor_get(v___x_3001_, 7);
                v_snapshotTasks_3010_ = leanh::lean_ctor_get(v___x_3001_, 8);
                v_isSharedCheck_3040_ = (!leanh::lean_is_exclusive(v___x_3001_)) as u8;
                if v_isSharedCheck_3040_ == 0 {
                    v___x_3012_ = v___x_3001_;
                    v_isShared_3013_ = v_isSharedCheck_3040_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3010_);
                    leanh::lean_inc(v_infoState_3009_);
                    leanh::lean_inc(v_messages_3008_);
                    leanh::lean_inc(v_cache_3007_);
                    leanh::lean_inc(v_traceState_3002_);
                    leanh::lean_inc(v_auxDeclNGen_3006_);
                    leanh::lean_inc(v_ngen_3005_);
                    leanh::lean_inc(v_nextMacroScope_3004_);
                    leanh::lean_inc(v_env_3003_);
                    leanh::lean_dec(v___x_3001_);
                    v___x_3012_ = leanh::lean_box(0);
                    v_isShared_3013_ = v_isSharedCheck_3040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3014_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3002_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3015_ = leanh::lean_ctor_get(v_traceState_3002_, 0);
                v_isSharedCheck_3039_ =
                    (!leanh::lean_is_exclusive(v_traceState_3002_)) as u8;
                if v_isSharedCheck_3039_ == 0 {
                    v___x_3017_ = v_traceState_3002_;
                    v_isShared_3018_ = v_isSharedCheck_3039_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3015_);
                    leanh::lean_dec(v_traceState_3002_);
                    v___x_3017_ = leanh::lean_box(0);
                    v_isShared_3018_ = v_isSharedCheck_3039_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3019_ = leanh::lean_box(0);
                v___x_3020_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0);
                v___x_3021_ = 0;
                v___x_3022_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1;
                v___x_3023_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_3023_, 0, v_cls_2988_);
                leanh::lean_ctor_set(v___x_3023_, 1, v___x_3019_);
                leanh::lean_ctor_set(v___x_3023_, 2, v___x_3022_);
                leanh::lean_ctor_set_float(
                    v___x_3023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3020_,
                );
                leanh::lean_ctor_set_float(
                    v___x_3023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3020_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3023_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3021_,
                );
                v___x_3024_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2;
                v___x_3025_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3025_, 0, v___x_3023_);
                leanh::lean_ctor_set(v___x_3025_, 1, v_a_2997_);
                leanh::lean_ctor_set(v___x_3025_, 2, v___x_3024_);
                leanh::lean_inc(v_ref_2995_);
                v___x_3026_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3026_, 0, v_ref_2995_);
                leanh::lean_ctor_set(v___x_3026_, 1, v___x_3025_);
                v___x_3027_ = l_Lean_PersistentArray_push___redArg(v_traces_3015_, v___x_3026_);
                if v_isShared_3018_ == 0 {
                    leanh::lean_ctor_set(v___x_3017_, 0, v___x_3027_);
                    v___x_3029_ = v___x_3017_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3027_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3038_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3014_,
                    );
                    v___x_3029_ = v_reuseFailAlloc_3038_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3013_ == 0 {
                    leanh::lean_ctor_set(v___x_3012_, 4, v___x_3029_);
                    v___x_3031_ = v___x_3012_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_env_3003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_nextMacroScope_3004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_ngen_3005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 3, v_auxDeclNGen_3006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 4, v___x_3029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 5, v_cache_3007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 6, v_messages_3008_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 7, v_infoState_3009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 8, v_snapshotTasks_3010_);
                    v___x_3031_ = v_reuseFailAlloc_3037_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3032_ = lean_st_ref_set(v___y_2993_, v___x_3031_);
                v___x_3033_ = leanh::lean_box(0);
                if v_isShared_3000_ == 0 {
                    leanh::lean_ctor_set(v___x_2999_, 0, v___x_3033_);
                    v___x_3035_ = v___x_2999_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
                    v___x_3035_ = v_reuseFailAlloc_3036_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___boxed(
    mut v_cls_3042_: *mut leanh::LeanObject,
    mut v_msg_3043_: *mut leanh::LeanObject,
    mut v___y_3044_: *mut leanh::LeanObject,
    mut v___y_3045_: *mut leanh::LeanObject,
    mut v___y_3046_: *mut leanh::LeanObject,
    mut v___y_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3049_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(
        v_cls_3042_,
        v_msg_3043_,
        v___y_3044_,
        v___y_3045_,
        v___y_3046_,
        v___y_3047_,
    );
    leanh::lean_dec(v___y_3047_);
    leanh::lean_dec_ref(v___y_3046_);
    leanh::lean_dec(v___y_3045_);
    leanh::lean_dec_ref(v___y_3044_);
    return v_res_3049_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(
    mut v_a_3050_: *mut leanh::LeanObject,
    mut v_x_3051_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3052_: u8 = 0;
    let mut v_key_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3051_) == 0 {
                    v___x_3052_ = 0;
                    return v___x_3052_;
                } else {
                    v_key_3053_ = leanh::lean_ctor_get(v_x_3051_, 0);
                    v_tail_3054_ = leanh::lean_ctor_get(v_x_3051_, 2);
                    v___x_3055_ = l_Lean_Meta_Grind_SplitInfo_beq(v_key_3053_, v_a_3050_);
                    if v___x_3055_ == 0 {
                        v_x_3051_ = v_tail_3054_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3055_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg___boxed(
    mut v_a_3057_: *mut leanh::LeanObject,
    mut v_x_3058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3059_: u8 = 0;
    let mut v_r_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_3057_, v_x_3058_);
    leanh::lean_dec(v_x_3058_);
    leanh::lean_dec_ref(v_a_3057_);
    v_r_3060_ = leanh::lean_box((v_res_3059_) as usize);
    return v_r_3060_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(
    mut v_x_3061_: *mut leanh::LeanObject,
    mut v_x_3062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3068_: u8 = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: u64 = 0;
    let mut v___x_3071_: u64 = 0;
    let mut v___x_3072_: u64 = 0;
    let mut v_fold_3073_: u64 = 0;
    let mut v___x_3074_: u64 = 0;
    let mut v___x_3075_: u64 = 0;
    let mut v___x_3076_: u64 = 0;
    let mut v___x_3077_: usize = 0;
    let mut v___x_3078_: usize = 0;
    let mut v___x_3079_: usize = 0;
    let mut v___x_3080_: usize = 0;
    let mut v___x_3081_: usize = 0;
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3062_) == 0 {
                    return v_x_3061_;
                } else {
                    v_key_3063_ = leanh::lean_ctor_get(v_x_3062_, 0);
                    v_value_3064_ = leanh::lean_ctor_get(v_x_3062_, 1);
                    v_tail_3065_ = leanh::lean_ctor_get(v_x_3062_, 2);
                    v_isSharedCheck_3088_ = (!leanh::lean_is_exclusive(v_x_3062_)) as u8;
                    if v_isSharedCheck_3088_ == 0 {
                        v___x_3067_ = v_x_3062_;
                        v_isShared_3068_ = v_isSharedCheck_3088_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3065_);
                        leanh::lean_inc(v_value_3064_);
                        leanh::lean_inc(v_key_3063_);
                        leanh::lean_dec(v_x_3062_);
                        v___x_3067_ = leanh::lean_box(0);
                        v_isShared_3068_ = v_isSharedCheck_3088_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3069_ = lean_array_get_size(v_x_3061_);
                v___x_3070_ = l_Lean_Meta_Grind_SplitInfo_hash(v_key_3063_);
                v___x_3071_ = 32u64;
                v___x_3072_ = lean_uint64_shift_right(v___x_3070_, v___x_3071_);
                v_fold_3073_ = lean_uint64_xor(v___x_3070_, v___x_3072_);
                v___x_3074_ = 16u64;
                v___x_3075_ = lean_uint64_shift_right(v_fold_3073_, v___x_3074_);
                v___x_3076_ = lean_uint64_xor(v_fold_3073_, v___x_3075_);
                v___x_3077_ = lean_uint64_to_usize(v___x_3076_);
                v___x_3078_ = lean_usize_of_nat(v___x_3069_);
                v___x_3079_ = 1usize;
                v___x_3080_ = lean_usize_sub(v___x_3078_, v___x_3079_);
                v___x_3081_ = lean_usize_land(v___x_3077_, v___x_3080_);
                v___x_3082_ = lean_array_uget_borrowed(v_x_3061_, v___x_3081_);
                leanh::lean_inc(v___x_3082_);
                if v_isShared_3068_ == 0 {
                    leanh::lean_ctor_set(v___x_3067_, 2, v___x_3082_);
                    v___x_3084_ = v___x_3067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3087_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_key_3063_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_value_3064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3087_, 2, v___x_3082_);
                    v___x_3084_ = v_reuseFailAlloc_3087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3085_ = lean_array_uset(v_x_3061_, v___x_3081_, v___x_3084_);
                v_x_3061_ = v___x_3085_;
                v_x_3062_ = v_tail_3065_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(
    mut v_i_3089_: *mut leanh::LeanObject,
    mut v_source_3090_: *mut leanh::LeanObject,
    mut v_target_3091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v_es_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3092_ = lean_array_get_size(v_source_3090_);
                v___x_3093_ = lean_nat_dec_lt(v_i_3089_, v___x_3092_);
                if v___x_3093_ == 0 {
                    leanh::lean_dec_ref(v_source_3090_);
                    leanh::lean_dec(v_i_3089_);
                    return v_target_3091_;
                } else {
                    v_es_3094_ = lean_array_fget(v_source_3090_, v_i_3089_);
                    v___x_3095_ = leanh::lean_box(0);
                    v_source_3096_ = lean_array_fset(v_source_3090_, v_i_3089_, v___x_3095_);
                    v_target_3097_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_target_3091_, v_es_3094_);
                    v___x_3098_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3099_ = lean_nat_add(v_i_3089_, v___x_3098_);
                    leanh::lean_dec(v_i_3089_);
                    v_i_3089_ = v___x_3099_;
                    v_source_3090_ = v_source_3096_;
                    v_target_3091_ = v_target_3097_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(
    mut v_data_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = lean_array_get_size(v_data_3101_);
    v___x_3103_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3104_ = lean_nat_mul(v___x_3102_, v___x_3103_);
    v___x_3105_ = leanh::lean_unsigned_to_nat(0);
    v___x_3106_ = leanh::lean_box(0);
    v___x_3107_ = lean_mk_array(v_nbuckets_3104_, v___x_3106_);
    v___x_3108_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v___x_3105_, v_data_3101_, v___x_3107_);
    return v___x_3108_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(
    mut v_m_3109_: *mut leanh::LeanObject,
    mut v_a_3110_: *mut leanh::LeanObject,
    mut v_b_3111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u64 = 0;
    let mut v___x_3116_: u64 = 0;
    let mut v___x_3117_: u64 = 0;
    let mut v_fold_3118_: u64 = 0;
    let mut v___x_3119_: u64 = 0;
    let mut v___x_3120_: u64 = 0;
    let mut v___x_3121_: u64 = 0;
    let mut v___x_3122_: usize = 0;
    let mut v___x_3123_: usize = 0;
    let mut v___x_3124_: usize = 0;
    let mut v___x_3125_: usize = 0;
    let mut v___x_3126_: usize = 0;
    let mut v_bkt_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v_val_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3149_: u8 = 0;
    let mut v_unused_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3112_ = leanh::lean_ctor_get(v_m_3109_, 0);
                v_buckets_3113_ = leanh::lean_ctor_get(v_m_3109_, 1);
                v___x_3114_ = lean_array_get_size(v_buckets_3113_);
                v___x_3115_ = l_Lean_Meta_Grind_SplitInfo_hash(v_a_3110_);
                v___x_3116_ = 32u64;
                v___x_3117_ = lean_uint64_shift_right(v___x_3115_, v___x_3116_);
                v_fold_3118_ = lean_uint64_xor(v___x_3115_, v___x_3117_);
                v___x_3119_ = 16u64;
                v___x_3120_ = lean_uint64_shift_right(v_fold_3118_, v___x_3119_);
                v___x_3121_ = lean_uint64_xor(v_fold_3118_, v___x_3120_);
                v___x_3122_ = lean_uint64_to_usize(v___x_3121_);
                v___x_3123_ = lean_usize_of_nat(v___x_3114_);
                v___x_3124_ = 1usize;
                v___x_3125_ = lean_usize_sub(v___x_3123_, v___x_3124_);
                v___x_3126_ = lean_usize_land(v___x_3122_, v___x_3125_);
                v_bkt_3127_ = lean_array_uget_borrowed(v_buckets_3113_, v___x_3126_);
                v___x_3128_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_3110_, v_bkt_3127_);
                if v___x_3128_ == 0 {
                    leanh::lean_inc_ref(v_buckets_3113_);
                    leanh::lean_inc(v_size_3112_);
                    v_isSharedCheck_3149_ = (!leanh::lean_is_exclusive(v_m_3109_)) as u8;
                    if v_isSharedCheck_3149_ == 0 {
                        v_unused_3150_ = leanh::lean_ctor_get(v_m_3109_, 1);
                        leanh::lean_dec(v_unused_3150_);
                        v_unused_3151_ = leanh::lean_ctor_get(v_m_3109_, 0);
                        leanh::lean_dec(v_unused_3151_);
                        v___x_3130_ = v_m_3109_;
                        v_isShared_3131_ = v_isSharedCheck_3149_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3109_);
                        v___x_3130_ = leanh::lean_box(0);
                        v_isShared_3131_ = v_isSharedCheck_3149_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3111_);
                    leanh::lean_dec_ref(v_a_3110_);
                    return v_m_3109_;
                }
            }
            1 => {
                v___x_3132_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3133_ = lean_nat_add(v_size_3112_, v___x_3132_);
                leanh::lean_dec(v_size_3112_);
                leanh::lean_inc(v_bkt_3127_);
                v___x_3134_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3134_, 0, v_a_3110_);
                leanh::lean_ctor_set(v___x_3134_, 1, v_b_3111_);
                leanh::lean_ctor_set(v___x_3134_, 2, v_bkt_3127_);
                v_buckets_x27_3135_ = lean_array_uset(v_buckets_3113_, v___x_3126_, v___x_3134_);
                v___x_3136_ = leanh::lean_unsigned_to_nat(4);
                v___x_3137_ = lean_nat_mul(v_size_x27_3133_, v___x_3136_);
                v___x_3138_ = leanh::lean_unsigned_to_nat(3);
                v___x_3139_ = lean_nat_div(v___x_3137_, v___x_3138_);
                leanh::lean_dec(v___x_3137_);
                v___x_3140_ = lean_array_get_size(v_buckets_x27_3135_);
                v___x_3141_ = lean_nat_dec_le(v___x_3139_, v___x_3140_);
                leanh::lean_dec(v___x_3139_);
                if v___x_3141_ == 0 {
                    v_val_3142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_buckets_x27_3135_);
                    if v_isShared_3131_ == 0 {
                        leanh::lean_ctor_set(v___x_3130_, 1, v_val_3142_);
                        leanh::lean_ctor_set(v___x_3130_, 0, v_size_x27_3133_);
                        v___x_3144_ = v___x_3130_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3145_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_size_x27_3133_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_val_3142_);
                        v___x_3144_ = v_reuseFailAlloc_3145_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_3131_ == 0 {
                        leanh::lean_ctor_set(v___x_3130_, 1, v_buckets_x27_3135_);
                        leanh::lean_ctor_set(v___x_3130_, 0, v_size_x27_3133_);
                        v___x_3147_ = v___x_3130_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3148_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_size_x27_3133_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_buckets_x27_3135_);
                        v___x_3147_ = v_reuseFailAlloc_3148_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3144_;
            }
            3 => {
                return v___x_3147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(
    mut v_ctx_3152_: *mut leanh::LeanObject,
    mut v_val_3153_: *mut leanh::LeanObject,
    mut v___x_3154_: *mut leanh::LeanObject,
    mut v___x_3155_: *mut leanh::LeanObject,
    mut v_as_x27_3156_: *mut leanh::LeanObject,
    mut v_b_3157_: *mut leanh::LeanObject,
    mut v___y_3158_: *mut leanh::LeanObject,
    mut v___y_3159_: *mut leanh::LeanObject,
    mut v___y_3160_: *mut leanh::LeanObject,
    mut v___y_3161_: *mut leanh::LeanObject,
    mut v___y_3162_: *mut leanh::LeanObject,
    mut v___y_3163_: *mut leanh::LeanObject,
    mut v___y_3164_: *mut leanh::LeanObject,
    mut v___y_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqAssignment_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v_a_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_a_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3156_) == 0 {
                    leanh::lean_dec(v___x_3155_);
                    leanh::lean_dec_ref(v___x_3154_);
                    leanh::lean_dec_ref(v_val_3153_);
                    leanh::lean_dec_ref(v_ctx_3152_);
                    v___x_3169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3169_, 0, v_b_3157_);
                    return v___x_3169_;
                } else {
                    v_head_3170_ = leanh::lean_ctor_get(v_as_x27_3156_, 0);
                    v_tail_3171_ = leanh::lean_ctor_get(v_as_x27_3156_, 1);
                    v_eqAssignment_3172_ = leanh::lean_ctor_get(v_ctx_3152_, 2);
                    v_arg_3173_ = leanh::lean_ctor_get(v_head_3170_, 0);
                    leanh::lean_inc_ref(v_eqAssignment_3172_);
                    leanh::lean_inc(v___y_3167_);
                    leanh::lean_inc_ref(v___y_3166_);
                    leanh::lean_inc(v___y_3165_);
                    leanh::lean_inc_ref(v___y_3164_);
                    leanh::lean_inc(v___y_3163_);
                    leanh::lean_inc_ref(v___y_3162_);
                    leanh::lean_inc(v___y_3161_);
                    leanh::lean_inc_ref(v___y_3160_);
                    leanh::lean_inc(v___y_3159_);
                    leanh::lean_inc(v___y_3158_);
                    leanh::lean_inc_ref(v_arg_3173_);
                    leanh::lean_inc_ref(v_val_3153_);
                    v___x_3174_ = leanh::lean_apply_13(
                        v_eqAssignment_3172_,
                        v_val_3153_,
                        v_arg_3173_,
                        v___y_3158_,
                        v___y_3159_,
                        v___y_3160_,
                        v___y_3161_,
                        v___y_3162_,
                        v___y_3163_,
                        v___y_3164_,
                        v___y_3165_,
                        v___y_3166_,
                        v___y_3167_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3174_) == 0 {
                        v_a_3175_ = leanh::lean_ctor_get(v___x_3174_, 0);
                        leanh::lean_inc(v_a_3175_);
                        leanh::lean_dec_ref_known(v___x_3174_, 1);
                        v___x_3176_ = (leanh::lean_unbox(v_a_3175_) as u8);
                        leanh::lean_dec(v_a_3175_);
                        if v___x_3176_ == 0 {
                            v_as_x27_3156_ = v_tail_3171_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_inc_ref(v_arg_3173_);
                            leanh::lean_inc_ref(v_val_3153_);
                            v___x_3178_ = l_Lean_Meta_Grind_hasSameType(
                                v_val_3153_,
                                v_arg_3173_,
                                v___y_3164_,
                                v___y_3165_,
                                v___y_3166_,
                                v___y_3167_,
                            );
                            if leanh::lean_obj_tag(v___x_3178_) == 0 {
                                v_a_3179_ = leanh::lean_ctor_get(v___x_3178_, 0);
                                leanh::lean_inc(v_a_3179_);
                                leanh::lean_dec_ref_known(v___x_3178_, 1);
                                v___x_3180_ = (leanh::lean_unbox(v_a_3179_) as u8);
                                leanh::lean_dec(v_a_3179_);
                                if v___x_3180_ == 0 {
                                    v_as_x27_3156_ = v_tail_3171_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_inc(v___x_3155_);
                                    leanh::lean_inc(v_head_3170_);
                                    leanh::lean_inc_ref(v___x_3154_);
                                    v___x_3182_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v___x_3154_, v_head_3170_, v___x_3155_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
                                    if leanh::lean_obj_tag(v___x_3182_) == 0 {
                                        v_a_3183_ = leanh::lean_ctor_get(v___x_3182_, 0);
                                        leanh::lean_inc(v_a_3183_);
                                        leanh::lean_dec_ref_known(v___x_3182_, 1);
                                        v___x_3184_ = leanh::lean_box(0);
                                        v___x_3185_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_b_3157_, v_a_3183_, v___x_3184_);
                                        v_as_x27_3156_ = v_tail_3171_;
                                        v_b_3157_ = v___x_3185_;
                                        state = 0;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v_b_3157_);
                                        leanh::lean_dec(v___x_3155_);
                                        leanh::lean_dec_ref(v___x_3154_);
                                        leanh::lean_dec_ref(v_val_3153_);
                                        leanh::lean_dec_ref(v_ctx_3152_);
                                        v_a_3187_ = leanh::lean_ctor_get(v___x_3182_, 0);
                                        v_isSharedCheck_3194_ =
                                            (!leanh::lean_is_exclusive(v___x_3182_)) as u8;
                                        if v_isSharedCheck_3194_ == 0 {
                                            v___x_3189_ = v___x_3182_;
                                            v_isShared_3190_ = v_isSharedCheck_3194_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3187_);
                                            leanh::lean_dec(v___x_3182_);
                                            v___x_3189_ = leanh::lean_box(0);
                                            v_isShared_3190_ = v_isSharedCheck_3194_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_b_3157_);
                                leanh::lean_dec(v___x_3155_);
                                leanh::lean_dec_ref(v___x_3154_);
                                leanh::lean_dec_ref(v_val_3153_);
                                leanh::lean_dec_ref(v_ctx_3152_);
                                v_a_3195_ = leanh::lean_ctor_get(v___x_3178_, 0);
                                v_isSharedCheck_3202_ =
                                    (!leanh::lean_is_exclusive(v___x_3178_)) as u8;
                                if v_isSharedCheck_3202_ == 0 {
                                    v___x_3197_ = v___x_3178_;
                                    v_isShared_3198_ = v_isSharedCheck_3202_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3195_);
                                    leanh::lean_dec(v___x_3178_);
                                    v___x_3197_ = leanh::lean_box(0);
                                    v_isShared_3198_ = v_isSharedCheck_3202_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_3157_);
                        leanh::lean_dec(v___x_3155_);
                        leanh::lean_dec_ref(v___x_3154_);
                        leanh::lean_dec_ref(v_val_3153_);
                        leanh::lean_dec_ref(v_ctx_3152_);
                        v_a_3203_ = leanh::lean_ctor_get(v___x_3174_, 0);
                        v_isSharedCheck_3210_ =
                            (!leanh::lean_is_exclusive(v___x_3174_)) as u8;
                        if v_isSharedCheck_3210_ == 0 {
                            v___x_3205_ = v___x_3174_;
                            v_isShared_3206_ = v_isSharedCheck_3210_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3203_);
                            leanh::lean_dec(v___x_3174_);
                            v___x_3205_ = leanh::lean_box(0);
                            v_isShared_3206_ = v_isSharedCheck_3210_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3190_ == 0 {
                    v___x_3192_ = v___x_3189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
                    v___x_3192_ = v_reuseFailAlloc_3193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3192_;
            }
            3 => {
                if v_isShared_3198_ == 0 {
                    v___x_3200_ = v___x_3197_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
                    v___x_3200_ = v_reuseFailAlloc_3201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3200_;
            }
            5 => {
                if v_isShared_3206_ == 0 {
                    v___x_3208_ = v___x_3205_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
                    v___x_3208_ = v_reuseFailAlloc_3209_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_3211_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_val_3212_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_3213_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_3214_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_as_x27_3215_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_3216_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_3217_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_3218_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_3219_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_3220_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_3221_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_3222_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_3223_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_3224_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_3225_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_3226_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3227_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3228_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(
        v_ctx_3211_,
        v_val_3212_,
        v___x_3213_,
        v___x_3214_,
        v_as_x27_3215_,
        v_b_3216_,
        v___y_3217_,
        v___y_3218_,
        v___y_3219_,
        v___y_3220_,
        v___y_3221_,
        v___y_3222_,
        v___y_3223_,
        v___y_3224_,
        v___y_3225_,
        v___y_3226_,
    );
    leanh::lean_dec(v___y_3226_);
    leanh::lean_dec_ref(v___y_3225_);
    leanh::lean_dec(v___y_3224_);
    leanh::lean_dec_ref(v___y_3223_);
    leanh::lean_dec(v___y_3222_);
    leanh::lean_dec_ref(v___y_3221_);
    leanh::lean_dec(v___y_3220_);
    leanh::lean_dec_ref(v___y_3219_);
    leanh::lean_dec(v___y_3218_);
    leanh::lean_dec(v___y_3217_);
    leanh::lean_dec(v_as_x27_3215_);
    return v_res_3228_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(
    mut v_a_3229_: *mut leanh::LeanObject,
    mut v_b_3230_: *mut leanh::LeanObject,
    mut v_x_3231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3238_: u8 = 0;
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3231_) == 0 {
                    leanh::lean_dec(v_b_3230_);
                    leanh::lean_dec_ref(v_a_3229_);
                    return v_x_3231_;
                } else {
                    v_key_3232_ = leanh::lean_ctor_get(v_x_3231_, 0);
                    v_value_3233_ = leanh::lean_ctor_get(v_x_3231_, 1);
                    v_tail_3234_ = leanh::lean_ctor_get(v_x_3231_, 2);
                    v_isSharedCheck_3246_ = (!leanh::lean_is_exclusive(v_x_3231_)) as u8;
                    if v_isSharedCheck_3246_ == 0 {
                        v___x_3236_ = v_x_3231_;
                        v_isShared_3237_ = v_isSharedCheck_3246_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3234_);
                        leanh::lean_inc(v_value_3233_);
                        leanh::lean_inc(v_key_3232_);
                        leanh::lean_dec(v_x_3231_);
                        v___x_3236_ = leanh::lean_box(0);
                        v_isShared_3237_ = v_isSharedCheck_3246_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3238_ = lean_expr_eqv(v_key_3232_, v_a_3229_);
                if v___x_3238_ == 0 {
                    v___x_3239_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_3229_, v_b_3230_, v_tail_3234_);
                    if v_isShared_3237_ == 0 {
                        leanh::lean_ctor_set(v___x_3236_, 2, v___x_3239_);
                        v___x_3241_ = v___x_3236_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3242_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_key_3232_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_value_3233_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 2, v___x_3239_);
                        v___x_3241_ = v_reuseFailAlloc_3242_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_3233_);
                    leanh::lean_dec(v_key_3232_);
                    if v_isShared_3237_ == 0 {
                        leanh::lean_ctor_set(v___x_3236_, 1, v_b_3230_);
                        leanh::lean_ctor_set(v___x_3236_, 0, v_a_3229_);
                        v___x_3244_ = v___x_3236_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3245_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3229_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_b_3230_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 2, v_tail_3234_);
                        v___x_3244_ = v_reuseFailAlloc_3245_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3241_;
            }
            3 => {
                return v___x_3244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(
    mut v_a_3247_: *mut leanh::LeanObject,
    mut v_x_3248_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3249_: u8 = 0;
    let mut v_key_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3248_) == 0 {
                    v___x_3249_ = 0;
                    return v___x_3249_;
                } else {
                    v_key_3250_ = leanh::lean_ctor_get(v_x_3248_, 0);
                    v_tail_3251_ = leanh::lean_ctor_get(v_x_3248_, 2);
                    v___x_3252_ = lean_expr_eqv(v_key_3250_, v_a_3247_);
                    if v___x_3252_ == 0 {
                        v_x_3248_ = v_tail_3251_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3252_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg___boxed(
    mut v_a_3254_: *mut leanh::LeanObject,
    mut v_x_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3256_: u8 = 0;
    let mut v_r_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3256_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_3254_, v_x_3255_);
    leanh::lean_dec(v_x_3255_);
    leanh::lean_dec_ref(v_a_3254_);
    v_r_3257_ = leanh::lean_box((v_res_3256_) as usize);
    return v_r_3257_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(
    mut v_x_3258_: *mut leanh::LeanObject,
    mut v_x_3259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: u64 = 0;
    let mut v___x_3268_: u64 = 0;
    let mut v___x_3269_: u64 = 0;
    let mut v_fold_3270_: u64 = 0;
    let mut v___x_3271_: u64 = 0;
    let mut v___x_3272_: u64 = 0;
    let mut v___x_3273_: u64 = 0;
    let mut v___x_3274_: usize = 0;
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: usize = 0;
    let mut v___x_3278_: usize = 0;
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3259_) == 0 {
                    return v_x_3258_;
                } else {
                    v_key_3260_ = leanh::lean_ctor_get(v_x_3259_, 0);
                    v_value_3261_ = leanh::lean_ctor_get(v_x_3259_, 1);
                    v_tail_3262_ = leanh::lean_ctor_get(v_x_3259_, 2);
                    v_isSharedCheck_3285_ = (!leanh::lean_is_exclusive(v_x_3259_)) as u8;
                    if v_isSharedCheck_3285_ == 0 {
                        v___x_3264_ = v_x_3259_;
                        v_isShared_3265_ = v_isSharedCheck_3285_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3262_);
                        leanh::lean_inc(v_value_3261_);
                        leanh::lean_inc(v_key_3260_);
                        leanh::lean_dec(v_x_3259_);
                        v___x_3264_ = leanh::lean_box(0);
                        v_isShared_3265_ = v_isSharedCheck_3285_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3266_ = lean_array_get_size(v_x_3258_);
                v___x_3267_ =
                    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(
                        v_key_3260_,
                    );
                v___x_3268_ = 32u64;
                v___x_3269_ = lean_uint64_shift_right(v___x_3267_, v___x_3268_);
                v_fold_3270_ = lean_uint64_xor(v___x_3267_, v___x_3269_);
                v___x_3271_ = 16u64;
                v___x_3272_ = lean_uint64_shift_right(v_fold_3270_, v___x_3271_);
                v___x_3273_ = lean_uint64_xor(v_fold_3270_, v___x_3272_);
                v___x_3274_ = lean_uint64_to_usize(v___x_3273_);
                v___x_3275_ = lean_usize_of_nat(v___x_3266_);
                v___x_3276_ = 1usize;
                v___x_3277_ = lean_usize_sub(v___x_3275_, v___x_3276_);
                v___x_3278_ = lean_usize_land(v___x_3274_, v___x_3277_);
                v___x_3279_ = lean_array_uget_borrowed(v_x_3258_, v___x_3278_);
                leanh::lean_inc(v___x_3279_);
                if v_isShared_3265_ == 0 {
                    leanh::lean_ctor_set(v___x_3264_, 2, v___x_3279_);
                    v___x_3281_ = v___x_3264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_key_3260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_value_3261_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 2, v___x_3279_);
                    v___x_3281_ = v_reuseFailAlloc_3284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3282_ = lean_array_uset(v_x_3258_, v___x_3278_, v___x_3281_);
                v_x_3258_ = v___x_3282_;
                v_x_3259_ = v_tail_3262_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(
    mut v_i_3286_: *mut leanh::LeanObject,
    mut v_source_3287_: *mut leanh::LeanObject,
    mut v_target_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: u8 = 0;
    let mut v_es_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3289_ = lean_array_get_size(v_source_3287_);
                v___x_3290_ = lean_nat_dec_lt(v_i_3286_, v___x_3289_);
                if v___x_3290_ == 0 {
                    leanh::lean_dec_ref(v_source_3287_);
                    leanh::lean_dec(v_i_3286_);
                    return v_target_3288_;
                } else {
                    v_es_3291_ = lean_array_fget(v_source_3287_, v_i_3286_);
                    v___x_3292_ = leanh::lean_box(0);
                    v_source_3293_ = lean_array_fset(v_source_3287_, v_i_3286_, v___x_3292_);
                    v_target_3294_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_target_3288_, v_es_3291_);
                    v___x_3295_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3296_ = lean_nat_add(v_i_3286_, v___x_3295_);
                    leanh::lean_dec(v_i_3286_);
                    v_i_3286_ = v___x_3296_;
                    v_source_3287_ = v_source_3293_;
                    v_target_3288_ = v_target_3294_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(
    mut v_data_3298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3299_ = lean_array_get_size(v_data_3298_);
    v___x_3300_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3301_ = lean_nat_mul(v___x_3299_, v___x_3300_);
    v___x_3302_ = leanh::lean_unsigned_to_nat(0);
    v___x_3303_ = leanh::lean_box(0);
    v___x_3304_ = lean_mk_array(v_nbuckets_3301_, v___x_3303_);
    v___x_3305_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v___x_3302_, v_data_3298_, v___x_3304_);
    return v___x_3305_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(
    mut v_m_3306_: *mut leanh::LeanObject,
    mut v_a_3307_: *mut leanh::LeanObject,
    mut v_b_3308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: u64 = 0;
    let mut v___x_3316_: u64 = 0;
    let mut v___x_3317_: u64 = 0;
    let mut v_fold_3318_: u64 = 0;
    let mut v___x_3319_: u64 = 0;
    let mut v___x_3320_: u64 = 0;
    let mut v___x_3321_: u64 = 0;
    let mut v___x_3322_: usize = 0;
    let mut v___x_3323_: usize = 0;
    let mut v___x_3324_: usize = 0;
    let mut v___x_3325_: usize = 0;
    let mut v___x_3326_: usize = 0;
    let mut v_bkt_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: u8 = 0;
    let mut v_val_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3309_ = leanh::lean_ctor_get(v_m_3306_, 0);
                v_buckets_3310_ = leanh::lean_ctor_get(v_m_3306_, 1);
                v_isSharedCheck_3353_ = (!leanh::lean_is_exclusive(v_m_3306_)) as u8;
                if v_isSharedCheck_3353_ == 0 {
                    v___x_3312_ = v_m_3306_;
                    v_isShared_3313_ = v_isSharedCheck_3353_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3310_);
                    leanh::lean_inc(v_size_3309_);
                    leanh::lean_dec(v_m_3306_);
                    v___x_3312_ = leanh::lean_box(0);
                    v_isShared_3313_ = v_isSharedCheck_3353_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3314_ = lean_array_get_size(v_buckets_3310_);
                v___x_3315_ =
                    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(
                        v_a_3307_,
                    );
                v___x_3316_ = 32u64;
                v___x_3317_ = lean_uint64_shift_right(v___x_3315_, v___x_3316_);
                v_fold_3318_ = lean_uint64_xor(v___x_3315_, v___x_3317_);
                v___x_3319_ = 16u64;
                v___x_3320_ = lean_uint64_shift_right(v_fold_3318_, v___x_3319_);
                v___x_3321_ = lean_uint64_xor(v_fold_3318_, v___x_3320_);
                v___x_3322_ = lean_uint64_to_usize(v___x_3321_);
                v___x_3323_ = lean_usize_of_nat(v___x_3314_);
                v___x_3324_ = 1usize;
                v___x_3325_ = lean_usize_sub(v___x_3323_, v___x_3324_);
                v___x_3326_ = lean_usize_land(v___x_3322_, v___x_3325_);
                v_bkt_3327_ = lean_array_uget_borrowed(v_buckets_3310_, v___x_3326_);
                v___x_3328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_3307_, v_bkt_3327_);
                if v___x_3328_ == 0 {
                    v___x_3329_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3330_ = lean_nat_add(v_size_3309_, v___x_3329_);
                    leanh::lean_dec(v_size_3309_);
                    leanh::lean_inc(v_bkt_3327_);
                    v___x_3331_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3331_, 0, v_a_3307_);
                    leanh::lean_ctor_set(v___x_3331_, 1, v_b_3308_);
                    leanh::lean_ctor_set(v___x_3331_, 2, v_bkt_3327_);
                    v_buckets_x27_3332_ =
                        lean_array_uset(v_buckets_3310_, v___x_3326_, v___x_3331_);
                    v___x_3333_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3334_ = lean_nat_mul(v_size_x27_3330_, v___x_3333_);
                    v___x_3335_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3336_ = lean_nat_div(v___x_3334_, v___x_3335_);
                    leanh::lean_dec(v___x_3334_);
                    v___x_3337_ = lean_array_get_size(v_buckets_x27_3332_);
                    v___x_3338_ = lean_nat_dec_le(v___x_3336_, v___x_3337_);
                    leanh::lean_dec(v___x_3336_);
                    if v___x_3338_ == 0 {
                        v_val_3339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_buckets_x27_3332_);
                        if v_isShared_3313_ == 0 {
                            leanh::lean_ctor_set(v___x_3312_, 1, v_val_3339_);
                            leanh::lean_ctor_set(v___x_3312_, 0, v_size_x27_3330_);
                            v___x_3341_ = v___x_3312_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3342_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3342_,
                                0,
                                v_size_x27_3330_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_val_3339_);
                            v___x_3341_ = v_reuseFailAlloc_3342_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3313_ == 0 {
                            leanh::lean_ctor_set(v___x_3312_, 1, v_buckets_x27_3332_);
                            leanh::lean_ctor_set(v___x_3312_, 0, v_size_x27_3330_);
                            v___x_3344_ = v___x_3312_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3345_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3345_,
                                0,
                                v_size_x27_3330_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3345_,
                                1,
                                v_buckets_x27_3332_,
                            );
                            v___x_3344_ = v_reuseFailAlloc_3345_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3327_);
                    v___x_3346_ = leanh::lean_box(0);
                    v_buckets_x27_3347_ =
                        lean_array_uset(v_buckets_3310_, v___x_3326_, v___x_3346_);
                    v___x_3348_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_3307_, v_b_3308_, v_bkt_3327_);
                    v___x_3349_ = lean_array_uset(v_buckets_x27_3347_, v___x_3326_, v___x_3348_);
                    if v_isShared_3313_ == 0 {
                        leanh::lean_ctor_set(v___x_3312_, 1, v___x_3349_);
                        v___x_3351_ = v___x_3312_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3352_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_size_3309_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3349_);
                        v___x_3351_ = v_reuseFailAlloc_3352_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3341_;
            }
            3 => {
                return v___x_3344_;
            }
            4 => {
                return v___x_3351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(
    mut v_val_3354_: *mut leanh::LeanObject,
    mut v_x_3355_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3356_: u8 = 0;
    let mut v_head_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3355_) == 0 {
                    v___x_3356_ = 0;
                    return v___x_3356_;
                } else {
                    v_head_3357_ = leanh::lean_ctor_get(v_x_3355_, 0);
                    v_tail_3358_ = leanh::lean_ctor_get(v_x_3355_, 1);
                    v_arg_3359_ = leanh::lean_ctor_get(v_head_3357_, 0);
                    v___x_3360_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_val_3354_,
                            v_arg_3359_,
                        );
                    if v___x_3360_ == 0 {
                        v_x_3355_ = v_tail_3358_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3360_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3___boxed(
    mut v_val_3362_: *mut leanh::LeanObject,
    mut v_x_3363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3364_: u8 = 0;
    let mut v_r_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3364_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_3362_, v_x_3363_);
    leanh::lean_dec(v_x_3363_);
    leanh::lean_dec_ref(v_val_3362_);
    v_r_3365_ = leanh::lean_box((v_res_3364_) as usize);
    return v_r_3365_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3;
    v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5;
    v___x_3378_ = l_Lean_Name_append(v___x_3377_, v___x_3376_);
    return v___x_3378_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7;
    v___x_3381_ = l_Lean_stringToMessageData(v___x_3380_);
    return v___x_3381_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9;
    v___x_3384_ = l_Lean_stringToMessageData(v___x_3383_);
    return v___x_3384_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(
    mut v_e_3385_: *mut leanh::LeanObject,
    mut v_ctx_3386_: *mut leanh::LeanObject,
    mut v___x_3387_: *mut leanh::LeanObject,
    mut v_as_3388_: *mut leanh::LeanObject,
    mut v_sz_3389_: usize,
    mut v_i_3390_: usize,
    mut v_b_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
    mut v___y_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
    mut v___y_3399_: *mut leanh::LeanObject,
    mut v___y_3400_: *mut leanh::LeanObject,
    mut v___y_3401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: usize = 0;
    let mut v___x_3406_: usize = 0;
    let mut v___x_3408_: u8 = 0;
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3415_: u8 = 0;
    let mut v_fst_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3420_: u8 = 0;
    let mut v_map_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3437_: u8 = 0;
    let mut v___y_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3466_: u8 = 0;
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_hasTheoryVar_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: u8 = 0;
    let mut v_options_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3483_: u8 = 0;
    let mut v_inheritedTraceOptions_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: u8 = 0;
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3504_: u8 = 0;
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3508_: u8 = 0;
    let mut v_reuseFailAlloc_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3513_: u8 = 0;
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3408_ = lean_usize_dec_lt(v_i_3390_, v_sz_3389_);
                if v___x_3408_ == 0 {
                    leanh::lean_dec_ref(v___x_3387_);
                    leanh::lean_dec_ref(v_ctx_3386_);
                    leanh::lean_dec_ref(v_e_3385_);
                    v___x_3409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3409_, 0, v_b_3391_);
                    return v___x_3409_;
                } else {
                    v___x_3410_ = lean_st_ref_get(v___y_3392_);
                    v_snd_3411_ = leanh::lean_ctor_get(v_b_3391_, 1);
                    v_fst_3412_ = leanh::lean_ctor_get(v_b_3391_, 0);
                    v_isSharedCheck_3522_ = (!leanh::lean_is_exclusive(v_b_3391_)) as u8;
                    if v_isSharedCheck_3522_ == 0 {
                        v___x_3414_ = v_b_3391_;
                        v_isShared_3415_ = v_isSharedCheck_3522_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3411_);
                        leanh::lean_inc(v_fst_3412_);
                        leanh::lean_dec(v_b_3391_);
                        v___x_3414_ = leanh::lean_box(0);
                        v_isShared_3415_ = v_isSharedCheck_3522_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3405_ = 1usize;
                v___x_3406_ = lean_usize_add(v_i_3390_, v___x_3405_);
                v_i_3390_ = v___x_3406_;
                v_b_3391_ = v_a_3404_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_3416_ = leanh::lean_ctor_get(v_snd_3411_, 0);
                v_snd_3417_ = leanh::lean_ctor_get(v_snd_3411_, 1);
                v_isSharedCheck_3521_ = (!leanh::lean_is_exclusive(v_snd_3411_)) as u8;
                if v_isSharedCheck_3521_ == 0 {
                    v___x_3419_ = v_snd_3411_;
                    v_isShared_3420_ = v_isSharedCheck_3521_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3417_);
                    leanh::lean_inc(v_fst_3416_);
                    leanh::lean_dec(v_snd_3411_);
                    v___x_3419_ = leanh::lean_box(0);
                    v_isShared_3420_ = v_isSharedCheck_3521_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_3432_ = lean_array_uget_borrowed(v_as_3388_, v_i_3390_);
                v___x_3433_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_3410_, v_a_3432_);
                leanh::lean_dec(v___x_3410_);
                if leanh::lean_obj_tag(v___x_3433_) == 1 {
                    v_val_3434_ = leanh::lean_ctor_get(v___x_3433_, 0);
                    v_isSharedCheck_3518_ = (!leanh::lean_is_exclusive(v___x_3433_)) as u8;
                    if v_isSharedCheck_3518_ == 0 {
                        v___x_3436_ = v___x_3433_;
                        v_isShared_3437_ = v_isSharedCheck_3518_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3434_);
                        leanh::lean_dec(v___x_3433_);
                        v___x_3436_ = leanh::lean_box(0);
                        v_isShared_3437_ = v_isSharedCheck_3518_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3433_);
                    leanh::lean_del_object(v___x_3419_);
                    leanh::lean_del_object(v___x_3414_);
                    v___x_3519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3519_, 0, v_fst_3416_);
                    leanh::lean_ctor_set(v___x_3519_, 1, v_snd_3417_);
                    v___x_3520_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3520_, 0, v_fst_3412_);
                    leanh::lean_ctor_set(v___x_3520_, 1, v___x_3519_);
                    v_a_3404_ = v___x_3520_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_3424_ = leanh::lean_unsigned_to_nat(1);
                v___x_3425_ = lean_nat_add(v_snd_3417_, v___x_3424_);
                leanh::lean_dec(v_snd_3417_);
                if v_isShared_3420_ == 0 {
                    leanh::lean_ctor_set(v___x_3419_, 1, v___x_3425_);
                    leanh::lean_ctor_set(v___x_3419_, 0, v_candidates_3423_);
                    v___x_3427_ = v___x_3419_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_candidates_3423_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3425_);
                    v___x_3427_ = v_reuseFailAlloc_3431_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3415_ == 0 {
                    leanh::lean_ctor_set(v___x_3414_, 1, v___x_3427_);
                    leanh::lean_ctor_set(v___x_3414_, 0, v_map_3422_);
                    v___x_3429_ = v___x_3414_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3430_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_map_3422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3427_);
                    v___x_3429_ = v_reuseFailAlloc_3430_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_3404_ = v___x_3429_;
                state = 1;
                continue;
            }
            7 => {
                v_hasTheoryVar_3478_ = leanh::lean_ctor_get(v_ctx_3386_, 1);
                leanh::lean_inc_ref(v_hasTheoryVar_3478_);
                leanh::lean_inc(v___y_3401_);
                leanh::lean_inc_ref(v___y_3400_);
                leanh::lean_inc(v___y_3399_);
                leanh::lean_inc_ref(v___y_3398_);
                leanh::lean_inc(v___y_3397_);
                leanh::lean_inc_ref(v___y_3396_);
                leanh::lean_inc(v___y_3395_);
                leanh::lean_inc_ref(v___y_3394_);
                leanh::lean_inc(v___y_3393_);
                leanh::lean_inc(v___y_3392_);
                leanh::lean_inc(v_val_3434_);
                v___x_3479_ = leanh::lean_apply_12(
                    v_hasTheoryVar_3478_,
                    v_val_3434_,
                    v___y_3392_,
                    v___y_3393_,
                    v___y_3394_,
                    v___y_3395_,
                    v___y_3396_,
                    v___y_3397_,
                    v___y_3398_,
                    v___y_3399_,
                    v___y_3400_,
                    v___y_3401_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3479_) == 0 {
                    v_a_3480_ = leanh::lean_ctor_get(v___x_3479_, 0);
                    leanh::lean_inc(v_a_3480_);
                    leanh::lean_dec_ref_known(v___x_3479_, 1);
                    v___x_3481_ = (leanh::lean_unbox(v_a_3480_) as u8);
                    leanh::lean_dec(v_a_3480_);
                    if v___x_3481_ == 0 {
                        leanh::lean_del_object(v___x_3436_);
                        leanh::lean_dec(v_val_3434_);
                        v_map_3422_ = v_fst_3412_;
                        v_candidates_3423_ = v_fst_3416_;
                        state = 4;
                        continue;
                    } else {
                        v_options_3482_ = leanh::lean_ctor_get(v___y_3400_, 2);
                        v_hasTrace_3483_ = leanh::lean_ctor_get_uint8(
                            v_options_3482_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3483_ == 0 {
                            leanh::lean_del_object(v___x_3436_);
                            v___y_3439_ = v___y_3392_;
                            v___y_3440_ = v___y_3393_;
                            v___y_3441_ = v___y_3394_;
                            v___y_3442_ = v___y_3395_;
                            v___y_3443_ = v___y_3396_;
                            v___y_3444_ = v___y_3397_;
                            v___y_3445_ = v___y_3398_;
                            v___y_3446_ = v___y_3399_;
                            v___y_3447_ = v___y_3400_;
                            v___y_3448_ = v___y_3401_;
                            state = 8;
                            continue;
                        } else {
                            v_inheritedTraceOptions_3484_ =
                                leanh::lean_ctor_get(v___y_3400_, 13);
                            v___x_3485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3;
                            v___x_3486_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
                            v___x_3487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3484_,
                                v_options_3482_,
                                v___x_3486_,
                            );
                            if v___x_3487_ == 0 {
                                leanh::lean_del_object(v___x_3436_);
                                v___y_3439_ = v___y_3392_;
                                v___y_3440_ = v___y_3393_;
                                v___y_3441_ = v___y_3394_;
                                v___y_3442_ = v___y_3395_;
                                v___y_3443_ = v___y_3396_;
                                v___y_3444_ = v___y_3397_;
                                v___y_3445_ = v___y_3398_;
                                v___y_3446_ = v___y_3399_;
                                v___y_3447_ = v___y_3400_;
                                v___y_3448_ = v___y_3401_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_3434_);
                                v___x_3488_ = l_Lean_MessageData_ofExpr(v_val_3434_);
                                v___x_3489_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
                                v___x_3490_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3490_, 0, v___x_3488_);
                                leanh::lean_ctor_set(v___x_3490_, 1, v___x_3489_);
                                leanh::lean_inc_ref(v___x_3387_);
                                v___x_3491_ = l_Lean_MessageData_ofExpr(v___x_3387_);
                                v___x_3492_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3492_, 0, v___x_3490_);
                                leanh::lean_ctor_set(v___x_3492_, 1, v___x_3491_);
                                v___x_3493_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
                                v___x_3494_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3494_, 0, v___x_3492_);
                                leanh::lean_ctor_set(v___x_3494_, 1, v___x_3493_);
                                leanh::lean_inc(v_snd_3417_);
                                v___x_3495_ = l_Nat_reprFast(v_snd_3417_);
                                if v_isShared_3437_ == 0 {
                                    leanh::lean_ctor_set_tag(v___x_3436_, 3);
                                    leanh::lean_ctor_set(v___x_3436_, 0, v___x_3495_);
                                    v___x_3497_ = v___x_3436_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3509_ =
                                        leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3509_,
                                        0,
                                        v___x_3495_,
                                    );
                                    v___x_3497_ = v_reuseFailAlloc_3509_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3436_);
                    leanh::lean_dec(v_val_3434_);
                    leanh::lean_del_object(v___x_3419_);
                    leanh::lean_dec(v_snd_3417_);
                    leanh::lean_dec(v_fst_3416_);
                    leanh::lean_del_object(v___x_3414_);
                    leanh::lean_dec(v_fst_3412_);
                    leanh::lean_dec_ref(v___x_3387_);
                    leanh::lean_dec_ref(v_ctx_3386_);
                    leanh::lean_dec_ref(v_e_3385_);
                    v_a_3510_ = leanh::lean_ctor_get(v___x_3479_, 0);
                    v_isSharedCheck_3517_ = (!leanh::lean_is_exclusive(v___x_3479_)) as u8;
                    if v_isSharedCheck_3517_ == 0 {
                        v___x_3512_ = v___x_3479_;
                        v_isShared_3513_ = v_isSharedCheck_3517_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3510_);
                        leanh::lean_dec(v___x_3479_);
                        v___x_3512_ = leanh::lean_box(0);
                        v_isShared_3513_ = v_isSharedCheck_3517_;
                        state = 16;
                        continue;
                    }
                }
            }
            8 => {
                leanh::lean_inc_ref_n(v_e_3385_, 2);
                leanh::lean_inc(v_val_3434_);
                v___x_3449_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3449_, 0, v_val_3434_);
                leanh::lean_ctor_set(v___x_3449_, 1, v_e_3385_);
                v___x_3450_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(
                    v_e_3385_,
                    v_snd_3417_,
                    v___y_3445_,
                    v___y_3446_,
                    v___y_3447_,
                    v___y_3448_,
                );
                if leanh::lean_obj_tag(v___x_3450_) == 0 {
                    v_a_3451_ = leanh::lean_ctor_get(v___x_3450_, 0);
                    leanh::lean_inc(v_a_3451_);
                    leanh::lean_dec_ref_known(v___x_3450_, 1);
                    v___x_3452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_3412_, v_a_3451_);
                    if leanh::lean_obj_tag(v___x_3452_) == 1 {
                        v_val_3453_ = leanh::lean_ctor_get(v___x_3452_, 0);
                        leanh::lean_inc(v_val_3453_);
                        leanh::lean_dec_ref_known(v___x_3452_, 1);
                        v___x_3454_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(
                            v_val_3434_,
                            v_val_3453_,
                        );
                        if v___x_3454_ == 0 {
                            leanh::lean_inc(v_snd_3417_);
                            leanh::lean_inc_ref(v___x_3449_);
                            leanh::lean_inc_ref(v_ctx_3386_);
                            v___x_3455_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_3386_, v_val_3434_, v___x_3449_, v_snd_3417_, v_val_3453_, v_fst_3416_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
                            if leanh::lean_obj_tag(v___x_3455_) == 0 {
                                v_a_3456_ = leanh::lean_ctor_get(v___x_3455_, 0);
                                leanh::lean_inc(v_a_3456_);
                                leanh::lean_dec_ref_known(v___x_3455_, 1);
                                v___x_3457_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3457_, 0, v___x_3449_);
                                leanh::lean_ctor_set(v___x_3457_, 1, v_val_3453_);
                                v___x_3458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_3412_, v_a_3451_, v___x_3457_);
                                v_map_3422_ = v___x_3458_;
                                v_candidates_3423_ = v_a_3456_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_3453_);
                                leanh::lean_dec(v_a_3451_);
                                leanh::lean_dec_ref_known(v___x_3449_, 2);
                                leanh::lean_del_object(v___x_3419_);
                                leanh::lean_dec(v_snd_3417_);
                                leanh::lean_del_object(v___x_3414_);
                                leanh::lean_dec(v_fst_3412_);
                                leanh::lean_dec_ref(v___x_3387_);
                                leanh::lean_dec_ref(v_ctx_3386_);
                                leanh::lean_dec_ref(v_e_3385_);
                                v_a_3459_ = leanh::lean_ctor_get(v___x_3455_, 0);
                                v_isSharedCheck_3466_ =
                                    (!leanh::lean_is_exclusive(v___x_3455_)) as u8;
                                if v_isSharedCheck_3466_ == 0 {
                                    v___x_3461_ = v___x_3455_;
                                    v_isShared_3462_ = v_isSharedCheck_3466_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3459_);
                                    leanh::lean_dec(v___x_3455_);
                                    v___x_3461_ = leanh::lean_box(0);
                                    v_isShared_3462_ = v_isSharedCheck_3466_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_val_3453_);
                            leanh::lean_dec(v_a_3451_);
                            leanh::lean_dec_ref_known(v___x_3449_, 2);
                            leanh::lean_dec(v_val_3434_);
                            v_map_3422_ = v_fst_3412_;
                            v_candidates_3423_ = v_fst_3416_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3452_);
                        leanh::lean_dec(v_val_3434_);
                        v___x_3467_ = leanh::lean_box(0);
                        v___x_3468_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3468_, 0, v___x_3449_);
                        leanh::lean_ctor_set(v___x_3468_, 1, v___x_3467_);
                        v___x_3469_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_3412_, v_a_3451_, v___x_3468_);
                        v_map_3422_ = v___x_3469_;
                        v_candidates_3423_ = v_fst_3416_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_3449_, 2);
                    leanh::lean_dec(v_val_3434_);
                    leanh::lean_del_object(v___x_3419_);
                    leanh::lean_dec(v_snd_3417_);
                    leanh::lean_dec(v_fst_3416_);
                    leanh::lean_del_object(v___x_3414_);
                    leanh::lean_dec(v_fst_3412_);
                    leanh::lean_dec_ref(v___x_3387_);
                    leanh::lean_dec_ref(v_ctx_3386_);
                    leanh::lean_dec_ref(v_e_3385_);
                    v_a_3470_ = leanh::lean_ctor_get(v___x_3450_, 0);
                    v_isSharedCheck_3477_ = (!leanh::lean_is_exclusive(v___x_3450_)) as u8;
                    if v_isSharedCheck_3477_ == 0 {
                        v___x_3472_ = v___x_3450_;
                        v_isShared_3473_ = v_isSharedCheck_3477_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3470_);
                        leanh::lean_dec(v___x_3450_);
                        v___x_3472_ = leanh::lean_box(0);
                        v_isShared_3473_ = v_isSharedCheck_3477_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3462_ == 0 {
                    v___x_3464_ = v___x_3461_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3465_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
                    v___x_3464_ = v_reuseFailAlloc_3465_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3464_;
            }
            11 => {
                if v_isShared_3473_ == 0 {
                    v___x_3475_ = v___x_3472_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
                    v___x_3475_ = v_reuseFailAlloc_3476_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3475_;
            }
            13 => {
                v___x_3498_ = l_Lean_MessageData_ofFormat(v___x_3497_);
                v___x_3499_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3499_, 0, v___x_3494_);
                leanh::lean_ctor_set(v___x_3499_, 1, v___x_3498_);
                v___x_3500_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(
                    v___x_3485_,
                    v___x_3499_,
                    v___y_3398_,
                    v___y_3399_,
                    v___y_3400_,
                    v___y_3401_,
                );
                if leanh::lean_obj_tag(v___x_3500_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3500_, 1);
                    v___y_3439_ = v___y_3392_;
                    v___y_3440_ = v___y_3393_;
                    v___y_3441_ = v___y_3394_;
                    v___y_3442_ = v___y_3395_;
                    v___y_3443_ = v___y_3396_;
                    v___y_3444_ = v___y_3397_;
                    v___y_3445_ = v___y_3398_;
                    v___y_3446_ = v___y_3399_;
                    v___y_3447_ = v___y_3400_;
                    v___y_3448_ = v___y_3401_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3434_);
                    leanh::lean_del_object(v___x_3419_);
                    leanh::lean_dec(v_snd_3417_);
                    leanh::lean_dec(v_fst_3416_);
                    leanh::lean_del_object(v___x_3414_);
                    leanh::lean_dec(v_fst_3412_);
                    leanh::lean_dec_ref(v___x_3387_);
                    leanh::lean_dec_ref(v_ctx_3386_);
                    leanh::lean_dec_ref(v_e_3385_);
                    v_a_3501_ = leanh::lean_ctor_get(v___x_3500_, 0);
                    v_isSharedCheck_3508_ = (!leanh::lean_is_exclusive(v___x_3500_)) as u8;
                    if v_isSharedCheck_3508_ == 0 {
                        v___x_3503_ = v___x_3500_;
                        v_isShared_3504_ = v_isSharedCheck_3508_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3501_);
                        leanh::lean_dec(v___x_3500_);
                        v___x_3503_ = leanh::lean_box(0);
                        v_isShared_3504_ = v_isSharedCheck_3508_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3504_ == 0 {
                    v___x_3506_ = v___x_3503_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
                    v___x_3506_ = v_reuseFailAlloc_3507_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3506_;
            }
            16 => {
                if v_isShared_3513_ == 0 {
                    v___x_3515_ = v___x_3512_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
                    v___x_3515_ = v_reuseFailAlloc_3516_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_3523_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_ctx_3524_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_3525_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_as_3526_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_sz_3527_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_i_3528_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_b_3529_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_3530_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_3531_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_3532_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_3533_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_3534_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_3535_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_3536_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_3537_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_3538_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3539_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_3540_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_sz_boxed_3541_: usize = 0;
    let mut v_i_boxed_3542_: usize = 0;
    let mut v_res_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3541_ = leanh::lean_unbox_usize(v_sz_3527_);
    leanh::lean_dec(v_sz_3527_);
    v_i_boxed_3542_ = leanh::lean_unbox_usize(v_i_3528_);
    leanh::lean_dec(v_i_3528_);
    v_res_3543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_3523_, v_ctx_3524_, v___x_3525_, v_as_3526_, v_sz_boxed_3541_, v_i_boxed_3542_, v_b_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
    leanh::lean_dec(v___y_3539_);
    leanh::lean_dec_ref(v___y_3538_);
    leanh::lean_dec(v___y_3537_);
    leanh::lean_dec_ref(v___y_3536_);
    leanh::lean_dec(v___y_3535_);
    leanh::lean_dec_ref(v___y_3534_);
    leanh::lean_dec(v___y_3533_);
    leanh::lean_dec_ref(v___y_3532_);
    leanh::lean_dec(v___y_3531_);
    leanh::lean_dec(v___y_3530_);
    leanh::lean_dec_ref(v_as_3526_);
    return v_res_3543_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(
    mut v_ctx_3544_: *mut leanh::LeanObject,
    mut v_as_3545_: *mut leanh::LeanObject,
    mut v_sz_3546_: usize,
    mut v_i_3547_: usize,
    mut v_b_3548_: *mut leanh::LeanObject,
    mut v___y_3549_: *mut leanh::LeanObject,
    mut v___y_3550_: *mut leanh::LeanObject,
    mut v___y_3551_: *mut leanh::LeanObject,
    mut v___y_3552_: *mut leanh::LeanObject,
    mut v___y_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
    mut v___y_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v_fst_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3570_: u8 = 0;
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: usize = 0;
    let mut v___x_3577_: usize = 0;
    let mut v_reuseFailAlloc_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: u8 = 0;
    let mut v___x_3589_: u8 = 0;
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInterpreted_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    let mut v___x_3602_: u8 = 0;
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3612_: usize = 0;
    let mut v___x_3613_: usize = 0;
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3621_: u8 = 0;
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3625_: u8 = 0;
    let mut v_unused_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3630_: u8 = 0;
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_a_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v_a_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3655_: u8 = 0;
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: u8 = 0;
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v_unused_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3560_ = lean_usize_dec_lt(v_i_3547_, v_sz_3546_);
                if v___x_3560_ == 0 {
                    leanh::lean_dec_ref(v_ctx_3544_);
                    v___x_3561_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3561_, 0, v_b_3548_);
                    return v___x_3561_;
                } else {
                    v_snd_3562_ = leanh::lean_ctor_get(v_b_3548_, 1);
                    v_isSharedCheck_3663_ = (!leanh::lean_is_exclusive(v_b_3548_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v_unused_3664_ = leanh::lean_ctor_get(v_b_3548_, 0);
                        leanh::lean_dec(v_unused_3664_);
                        v___x_3564_ = v_b_3548_;
                        v_isShared_3565_ = v_isSharedCheck_3663_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3562_);
                        leanh::lean_dec(v_b_3548_);
                        v___x_3564_ = leanh::lean_box(0);
                        v_isShared_3565_ = v_isSharedCheck_3663_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3566_ = leanh::lean_ctor_get(v_snd_3562_, 0);
                v_snd_3567_ = leanh::lean_ctor_get(v_snd_3562_, 1);
                v_isSharedCheck_3662_ = (!leanh::lean_is_exclusive(v_snd_3562_)) as u8;
                if v_isSharedCheck_3662_ == 0 {
                    v___x_3569_ = v_snd_3562_;
                    v_isShared_3570_ = v_isSharedCheck_3662_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3567_);
                    leanh::lean_inc(v_fst_3566_);
                    leanh::lean_dec(v_snd_3562_);
                    v___x_3569_ = leanh::lean_box(0);
                    v_isShared_3570_ = v_isSharedCheck_3662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3571_ = leanh::lean_box(0);
                v_a_3586_ = lean_array_uget_borrowed(v_as_3545_, v_i_3547_);
                v___x_3660_ = l_Lean_Expr_isApp(v_a_3586_);
                if v___x_3660_ == 0 {
                    v___y_3588_ = v___x_3660_;
                    state = 8;
                    continue;
                } else {
                    v___x_3661_ = l_Lean_Expr_isEq(v_a_3586_);
                    if v___x_3661_ == 0 {
                        v___y_3588_ = v___x_3660_;
                        state = 8;
                        continue;
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3570_ == 0 {
                    leanh::lean_ctor_set(v___x_3569_, 1, v_a_3573_);
                    leanh::lean_ctor_set(v___x_3569_, 0, v___x_3571_);
                    v___x_3575_ = v___x_3569_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3571_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_a_3573_);
                    v___x_3575_ = v_reuseFailAlloc_3579_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3576_ = 1usize;
                v___x_3577_ = lean_usize_add(v_i_3547_, v___x_3576_);
                v_i_3547_ = v___x_3577_;
                v_b_3548_ = v___x_3575_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_3565_ == 0 {
                    leanh::lean_ctor_set(v___x_3564_, 1, v_snd_3567_);
                    leanh::lean_ctor_set(v___x_3564_, 0, v_fst_3566_);
                    v___x_3582_ = v___x_3564_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_fst_3566_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_snd_3567_);
                    v___x_3582_ = v_reuseFailAlloc_3583_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_3573_ = v___x_3582_;
                state = 3;
                continue;
            }
            7 => {
                v___x_3585_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3585_, 0, v_fst_3566_);
                leanh::lean_ctor_set(v___x_3585_, 1, v_snd_3567_);
                v_a_3573_ = v___x_3585_;
                state = 3;
                continue;
            }
            8 => {
                if v___y_3588_ == 0 {
                    state = 5;
                    continue;
                } else {
                    v___x_3589_ = l_Lean_Expr_isHEq(v_a_3586_);
                    if v___x_3589_ == 0 {
                        leanh::lean_del_object(v___x_3564_);
                        leanh::lean_inc(v_a_3586_);
                        v___x_3590_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                            v_a_3586_,
                            v___y_3549_,
                            v___y_3555_,
                            v___y_3556_,
                            v___y_3557_,
                            v___y_3558_,
                        );
                        if leanh::lean_obj_tag(v___x_3590_) == 0 {
                            v_a_3591_ = leanh::lean_ctor_get(v___x_3590_, 0);
                            leanh::lean_inc(v_a_3591_);
                            leanh::lean_dec_ref_known(v___x_3590_, 1);
                            v___x_3592_ = (leanh::lean_unbox(v_a_3591_) as u8);
                            leanh::lean_dec(v_a_3591_);
                            if v___x_3592_ == 0 {
                                v___x_3593_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3593_, 0, v_fst_3566_);
                                leanh::lean_ctor_set(v___x_3593_, 1, v_snd_3567_);
                                v_a_3573_ = v___x_3593_;
                                state = 3;
                                continue;
                            } else {
                                v_isInterpreted_3594_ = leanh::lean_ctor_get(v_ctx_3544_, 0);
                                leanh::lean_inc_ref(v_isInterpreted_3594_);
                                leanh::lean_inc(v___y_3558_);
                                leanh::lean_inc_ref(v___y_3557_);
                                leanh::lean_inc(v___y_3556_);
                                leanh::lean_inc_ref(v___y_3555_);
                                leanh::lean_inc(v___y_3554_);
                                leanh::lean_inc_ref(v___y_3553_);
                                leanh::lean_inc(v___y_3552_);
                                leanh::lean_inc_ref(v___y_3551_);
                                leanh::lean_inc(v___y_3550_);
                                leanh::lean_inc(v___y_3549_);
                                leanh::lean_inc(v_a_3586_);
                                v___x_3595_ = leanh::lean_apply_12(
                                    v_isInterpreted_3594_,
                                    v_a_3586_,
                                    v___y_3549_,
                                    v___y_3550_,
                                    v___y_3551_,
                                    v___y_3552_,
                                    v___y_3553_,
                                    v___y_3554_,
                                    v___y_3555_,
                                    v___y_3556_,
                                    v___y_3557_,
                                    v___y_3558_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_3595_) == 0 {
                                    v_a_3596_ = leanh::lean_ctor_get(v___x_3595_, 0);
                                    leanh::lean_inc(v_a_3596_);
                                    leanh::lean_dec_ref_known(v___x_3595_, 1);
                                    v___x_3597_ = (leanh::lean_unbox(v_a_3596_) as u8);
                                    leanh::lean_dec(v_a_3596_);
                                    if v___x_3597_ == 0 {
                                        v___x_3598_ = l_Lean_Expr_getAppFn(v_a_3586_);
                                        leanh::lean_inc_ref(v___x_3598_);
                                        v___x_3599_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_3598_, v___y_3557_, v___y_3558_);
                                        if leanh::lean_obj_tag(v___x_3599_) == 0 {
                                            v_a_3600_ = leanh::lean_ctor_get(v___x_3599_, 0);
                                            leanh::lean_inc(v_a_3600_);
                                            leanh::lean_dec_ref_known(v___x_3599_, 1);
                                            v___x_3601_ =
                                                (leanh::lean_unbox(v_a_3600_) as u8);
                                            leanh::lean_dec(v_a_3600_);
                                            if v___x_3601_ == 0 {
                                                v___x_3602_ =
                                                    l_Lean_Meta_Grind_isCastLikeFn(v___x_3598_);
                                                if v___x_3602_ == 0 {
                                                    v___x_3603_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v_dummy_3604_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
                                                    v_nargs_3605_ =
                                                        l_Lean_Expr_getAppNumArgs(v_a_3586_);
                                                    leanh::lean_inc(v_nargs_3605_);
                                                    v___x_3606_ =
                                                        lean_mk_array(v_nargs_3605_, v_dummy_3604_);
                                                    v___x_3607_ =
                                                        leanh::lean_unsigned_to_nat(1);
                                                    v___x_3608_ =
                                                        lean_nat_sub(v_nargs_3605_, v___x_3607_);
                                                    leanh::lean_dec(v_nargs_3605_);
                                                    leanh::lean_inc_n(v_a_3586_, 2);
                                                    v___x_3609_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3586_, v___x_3606_, v___x_3608_);
                                                    v___x_3610_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3610_,
                                                        0,
                                                        v_snd_3567_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3610_,
                                                        1,
                                                        v___x_3603_,
                                                    );
                                                    v___x_3611_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3611_,
                                                        0,
                                                        v_fst_3566_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3611_,
                                                        1,
                                                        v___x_3610_,
                                                    );
                                                    v_sz_3612_ = lean_array_size(v___x_3609_);
                                                    v___x_3613_ = 0usize;
                                                    leanh::lean_inc_ref(v_ctx_3544_);
                                                    v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_3586_, v_ctx_3544_, v___x_3598_, v___x_3609_, v_sz_3612_, v___x_3613_, v___x_3611_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
                                                    leanh::lean_dec_ref(v___x_3609_);
                                                    if leanh::lean_obj_tag(v___x_3614_) == 0
                                                    {
                                                        v_a_3615_ = leanh::lean_ctor_get(
                                                            v___x_3614_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_3615_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_3614_,
                                                            1,
                                                        );
                                                        v_snd_3616_ = leanh::lean_ctor_get(
                                                            v_a_3615_, 1,
                                                        );
                                                        leanh::lean_inc(v_snd_3616_);
                                                        v_fst_3617_ = leanh::lean_ctor_get(
                                                            v_a_3615_, 0,
                                                        );
                                                        leanh::lean_inc(v_fst_3617_);
                                                        leanh::lean_dec(v_a_3615_);
                                                        v_fst_3618_ = leanh::lean_ctor_get(
                                                            v_snd_3616_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3625_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v_snd_3616_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3625_ == 0 {
                                                            v_unused_3626_ =
                                                                leanh::lean_ctor_get(
                                                                    v_snd_3616_,
                                                                    1,
                                                                );
                                                            leanh::lean_dec(v_unused_3626_);
                                                            v___x_3620_ = v_snd_3616_;
                                                            v_isShared_3621_ =
                                                                v_isSharedCheck_3625_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_fst_3618_);
                                                            leanh::lean_dec(v_snd_3616_);
                                                            v___x_3620_ = leanh::lean_box(0);
                                                            v_isShared_3621_ =
                                                                v_isSharedCheck_3625_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_del_object(v___x_3569_);
                                                        leanh::lean_dec_ref(v_ctx_3544_);
                                                        v_a_3627_ = leanh::lean_ctor_get(
                                                            v___x_3614_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3634_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_3614_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3634_ == 0 {
                                                            v___x_3629_ = v___x_3614_;
                                                            v_isShared_3630_ =
                                                                v_isSharedCheck_3634_;
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_3627_);
                                                            leanh::lean_dec(v___x_3614_);
                                                            v___x_3629_ = leanh::lean_box(0);
                                                            v_isShared_3630_ =
                                                                v_isSharedCheck_3634_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_3598_);
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_3598_);
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_3598_);
                                            leanh::lean_del_object(v___x_3569_);
                                            leanh::lean_dec(v_snd_3567_);
                                            leanh::lean_dec(v_fst_3566_);
                                            leanh::lean_dec_ref(v_ctx_3544_);
                                            v_a_3635_ = leanh::lean_ctor_get(v___x_3599_, 0);
                                            v_isSharedCheck_3642_ =
                                                (!leanh::lean_is_exclusive(v___x_3599_))
                                                    as u8;
                                            if v_isSharedCheck_3642_ == 0 {
                                                v___x_3637_ = v___x_3599_;
                                                v_isShared_3638_ = v_isSharedCheck_3642_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3635_);
                                                leanh::lean_dec(v___x_3599_);
                                                v___x_3637_ = leanh::lean_box(0);
                                                v_isShared_3638_ = v_isSharedCheck_3642_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_3643_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3643_, 0, v_fst_3566_);
                                        leanh::lean_ctor_set(v___x_3643_, 1, v_snd_3567_);
                                        v_a_3573_ = v___x_3643_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_3569_);
                                    leanh::lean_dec(v_snd_3567_);
                                    leanh::lean_dec(v_fst_3566_);
                                    leanh::lean_dec_ref(v_ctx_3544_);
                                    v_a_3644_ = leanh::lean_ctor_get(v___x_3595_, 0);
                                    v_isSharedCheck_3651_ =
                                        (!leanh::lean_is_exclusive(v___x_3595_)) as u8;
                                    if v_isSharedCheck_3651_ == 0 {
                                        v___x_3646_ = v___x_3595_;
                                        v_isShared_3647_ = v_isSharedCheck_3651_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3644_);
                                        leanh::lean_dec(v___x_3595_);
                                        v___x_3646_ = leanh::lean_box(0);
                                        v_isShared_3647_ = v_isSharedCheck_3651_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_3569_);
                            leanh::lean_dec(v_snd_3567_);
                            leanh::lean_dec(v_fst_3566_);
                            leanh::lean_dec_ref(v_ctx_3544_);
                            v_a_3652_ = leanh::lean_ctor_get(v___x_3590_, 0);
                            v_isSharedCheck_3659_ =
                                (!leanh::lean_is_exclusive(v___x_3590_)) as u8;
                            if v_isSharedCheck_3659_ == 0 {
                                v___x_3654_ = v___x_3590_;
                                v_isShared_3655_ = v_isSharedCheck_3659_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3652_);
                                leanh::lean_dec(v___x_3590_);
                                v___x_3654_ = leanh::lean_box(0);
                                v_isShared_3655_ = v_isSharedCheck_3659_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3621_ == 0 {
                    leanh::lean_ctor_set(v___x_3620_, 1, v_fst_3618_);
                    leanh::lean_ctor_set(v___x_3620_, 0, v_fst_3617_);
                    v___x_3623_ = v___x_3620_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3624_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_fst_3617_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_fst_3618_);
                    v___x_3623_ = v_reuseFailAlloc_3624_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_3573_ = v___x_3623_;
                state = 3;
                continue;
            }
            11 => {
                if v_isShared_3630_ == 0 {
                    v___x_3632_ = v___x_3629_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
                    v___x_3632_ = v_reuseFailAlloc_3633_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3632_;
            }
            13 => {
                if v_isShared_3638_ == 0 {
                    v___x_3640_ = v___x_3637_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
                    v___x_3640_ = v_reuseFailAlloc_3641_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3640_;
            }
            15 => {
                if v_isShared_3647_ == 0 {
                    v___x_3649_ = v___x_3646_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3650_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
                    v___x_3649_ = v_reuseFailAlloc_3650_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3649_;
            }
            17 => {
                if v_isShared_3655_ == 0 {
                    v___x_3657_ = v___x_3654_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3658_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
                    v___x_3657_ = v_reuseFailAlloc_3658_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20___boxed(
    mut v_ctx_3665_: *mut leanh::LeanObject,
    mut v_as_3666_: *mut leanh::LeanObject,
    mut v_sz_3667_: *mut leanh::LeanObject,
    mut v_i_3668_: *mut leanh::LeanObject,
    mut v_b_3669_: *mut leanh::LeanObject,
    mut v___y_3670_: *mut leanh::LeanObject,
    mut v___y_3671_: *mut leanh::LeanObject,
    mut v___y_3672_: *mut leanh::LeanObject,
    mut v___y_3673_: *mut leanh::LeanObject,
    mut v___y_3674_: *mut leanh::LeanObject,
    mut v___y_3675_: *mut leanh::LeanObject,
    mut v___y_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3681_: usize = 0;
    let mut v_i_boxed_3682_: usize = 0;
    let mut v_res_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3681_ = leanh::lean_unbox_usize(v_sz_3667_);
    leanh::lean_dec(v_sz_3667_);
    v_i_boxed_3682_ = leanh::lean_unbox_usize(v_i_3668_);
    leanh::lean_dec(v_i_3668_);
    v_res_3683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_3665_, v_as_3666_, v_sz_boxed_3681_, v_i_boxed_3682_, v_b_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
    leanh::lean_dec(v___y_3679_);
    leanh::lean_dec_ref(v___y_3678_);
    leanh::lean_dec(v___y_3677_);
    leanh::lean_dec_ref(v___y_3676_);
    leanh::lean_dec(v___y_3675_);
    leanh::lean_dec_ref(v___y_3674_);
    leanh::lean_dec(v___y_3673_);
    leanh::lean_dec_ref(v___y_3672_);
    leanh::lean_dec(v___y_3671_);
    leanh::lean_dec(v___y_3670_);
    leanh::lean_dec_ref(v_as_3666_);
    return v_res_3683_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(
    mut v_ctx_3684_: *mut leanh::LeanObject,
    mut v_as_3685_: *mut leanh::LeanObject,
    mut v_sz_3686_: usize,
    mut v_i_3687_: usize,
    mut v_b_3688_: *mut leanh::LeanObject,
    mut v___y_3689_: *mut leanh::LeanObject,
    mut v___y_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
    mut v___y_3695_: *mut leanh::LeanObject,
    mut v___y_3696_: *mut leanh::LeanObject,
    mut v___y_3697_: *mut leanh::LeanObject,
    mut v___y_3698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3700_: u8 = 0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v_fst_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: usize = 0;
    let mut v___x_3717_: usize = 0;
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3728_: u8 = 0;
    let mut v___x_3729_: u8 = 0;
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: u8 = 0;
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInterpreted_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3752_: usize = 0;
    let mut v___x_3753_: usize = 0;
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3761_: u8 = 0;
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3765_: u8 = 0;
    let mut v_unused_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3770_: u8 = 0;
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3774_: u8 = 0;
    let mut v_a_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3778_: u8 = 0;
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3787_: u8 = 0;
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3791_: u8 = 0;
    let mut v_a_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: u8 = 0;
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_unused_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3700_ = lean_usize_dec_lt(v_i_3687_, v_sz_3686_);
                if v___x_3700_ == 0 {
                    leanh::lean_dec_ref(v_ctx_3684_);
                    v___x_3701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3701_, 0, v_b_3688_);
                    return v___x_3701_;
                } else {
                    v_snd_3702_ = leanh::lean_ctor_get(v_b_3688_, 1);
                    v_isSharedCheck_3803_ = (!leanh::lean_is_exclusive(v_b_3688_)) as u8;
                    if v_isSharedCheck_3803_ == 0 {
                        v_unused_3804_ = leanh::lean_ctor_get(v_b_3688_, 0);
                        leanh::lean_dec(v_unused_3804_);
                        v___x_3704_ = v_b_3688_;
                        v_isShared_3705_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3702_);
                        leanh::lean_dec(v_b_3688_);
                        v___x_3704_ = leanh::lean_box(0);
                        v_isShared_3705_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3706_ = leanh::lean_ctor_get(v_snd_3702_, 0);
                v_snd_3707_ = leanh::lean_ctor_get(v_snd_3702_, 1);
                v_isSharedCheck_3802_ = (!leanh::lean_is_exclusive(v_snd_3702_)) as u8;
                if v_isSharedCheck_3802_ == 0 {
                    v___x_3709_ = v_snd_3702_;
                    v_isShared_3710_ = v_isSharedCheck_3802_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3707_);
                    leanh::lean_inc(v_fst_3706_);
                    leanh::lean_dec(v_snd_3702_);
                    v___x_3709_ = leanh::lean_box(0);
                    v_isShared_3710_ = v_isSharedCheck_3802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3711_ = leanh::lean_box(0);
                v_a_3726_ = lean_array_uget_borrowed(v_as_3685_, v_i_3687_);
                v___x_3800_ = l_Lean_Expr_isApp(v_a_3726_);
                if v___x_3800_ == 0 {
                    v___y_3728_ = v___x_3800_;
                    state = 8;
                    continue;
                } else {
                    v___x_3801_ = l_Lean_Expr_isEq(v_a_3726_);
                    if v___x_3801_ == 0 {
                        v___y_3728_ = v___x_3800_;
                        state = 8;
                        continue;
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3710_ == 0 {
                    leanh::lean_ctor_set(v___x_3709_, 1, v_a_3713_);
                    leanh::lean_ctor_set(v___x_3709_, 0, v___x_3711_);
                    v___x_3715_ = v___x_3709_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_a_3713_);
                    v___x_3715_ = v_reuseFailAlloc_3719_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3716_ = 1usize;
                v___x_3717_ = lean_usize_add(v_i_3687_, v___x_3716_);
                v___x_3718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_3684_, v_as_3685_, v_sz_3686_, v___x_3717_, v___x_3715_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
                return v___x_3718_;
            }
            5 => {
                if v_isShared_3705_ == 0 {
                    leanh::lean_ctor_set(v___x_3704_, 1, v_snd_3707_);
                    leanh::lean_ctor_set(v___x_3704_, 0, v_fst_3706_);
                    v___x_3722_ = v___x_3704_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3723_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_fst_3706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_snd_3707_);
                    v___x_3722_ = v_reuseFailAlloc_3723_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_3713_ = v___x_3722_;
                state = 3;
                continue;
            }
            7 => {
                v___x_3725_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3725_, 0, v_fst_3706_);
                leanh::lean_ctor_set(v___x_3725_, 1, v_snd_3707_);
                v_a_3713_ = v___x_3725_;
                state = 3;
                continue;
            }
            8 => {
                if v___y_3728_ == 0 {
                    state = 5;
                    continue;
                } else {
                    v___x_3729_ = l_Lean_Expr_isHEq(v_a_3726_);
                    if v___x_3729_ == 0 {
                        leanh::lean_del_object(v___x_3704_);
                        leanh::lean_inc(v_a_3726_);
                        v___x_3730_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                            v_a_3726_,
                            v___y_3689_,
                            v___y_3695_,
                            v___y_3696_,
                            v___y_3697_,
                            v___y_3698_,
                        );
                        if leanh::lean_obj_tag(v___x_3730_) == 0 {
                            v_a_3731_ = leanh::lean_ctor_get(v___x_3730_, 0);
                            leanh::lean_inc(v_a_3731_);
                            leanh::lean_dec_ref_known(v___x_3730_, 1);
                            v___x_3732_ = (leanh::lean_unbox(v_a_3731_) as u8);
                            leanh::lean_dec(v_a_3731_);
                            if v___x_3732_ == 0 {
                                v___x_3733_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3733_, 0, v_fst_3706_);
                                leanh::lean_ctor_set(v___x_3733_, 1, v_snd_3707_);
                                v_a_3713_ = v___x_3733_;
                                state = 3;
                                continue;
                            } else {
                                v_isInterpreted_3734_ = leanh::lean_ctor_get(v_ctx_3684_, 0);
                                leanh::lean_inc_ref(v_isInterpreted_3734_);
                                leanh::lean_inc(v___y_3698_);
                                leanh::lean_inc_ref(v___y_3697_);
                                leanh::lean_inc(v___y_3696_);
                                leanh::lean_inc_ref(v___y_3695_);
                                leanh::lean_inc(v___y_3694_);
                                leanh::lean_inc_ref(v___y_3693_);
                                leanh::lean_inc(v___y_3692_);
                                leanh::lean_inc_ref(v___y_3691_);
                                leanh::lean_inc(v___y_3690_);
                                leanh::lean_inc(v___y_3689_);
                                leanh::lean_inc(v_a_3726_);
                                v___x_3735_ = leanh::lean_apply_12(
                                    v_isInterpreted_3734_,
                                    v_a_3726_,
                                    v___y_3689_,
                                    v___y_3690_,
                                    v___y_3691_,
                                    v___y_3692_,
                                    v___y_3693_,
                                    v___y_3694_,
                                    v___y_3695_,
                                    v___y_3696_,
                                    v___y_3697_,
                                    v___y_3698_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_3735_) == 0 {
                                    v_a_3736_ = leanh::lean_ctor_get(v___x_3735_, 0);
                                    leanh::lean_inc(v_a_3736_);
                                    leanh::lean_dec_ref_known(v___x_3735_, 1);
                                    v___x_3737_ = (leanh::lean_unbox(v_a_3736_) as u8);
                                    leanh::lean_dec(v_a_3736_);
                                    if v___x_3737_ == 0 {
                                        v___x_3738_ = l_Lean_Expr_getAppFn(v_a_3726_);
                                        leanh::lean_inc_ref(v___x_3738_);
                                        v___x_3739_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_3738_, v___y_3697_, v___y_3698_);
                                        if leanh::lean_obj_tag(v___x_3739_) == 0 {
                                            v_a_3740_ = leanh::lean_ctor_get(v___x_3739_, 0);
                                            leanh::lean_inc(v_a_3740_);
                                            leanh::lean_dec_ref_known(v___x_3739_, 1);
                                            v___x_3741_ =
                                                (leanh::lean_unbox(v_a_3740_) as u8);
                                            leanh::lean_dec(v_a_3740_);
                                            if v___x_3741_ == 0 {
                                                v___x_3742_ =
                                                    l_Lean_Meta_Grind_isCastLikeFn(v___x_3738_);
                                                if v___x_3742_ == 0 {
                                                    v___x_3743_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v_dummy_3744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
                                                    v_nargs_3745_ =
                                                        l_Lean_Expr_getAppNumArgs(v_a_3726_);
                                                    leanh::lean_inc(v_nargs_3745_);
                                                    v___x_3746_ =
                                                        lean_mk_array(v_nargs_3745_, v_dummy_3744_);
                                                    v___x_3747_ =
                                                        leanh::lean_unsigned_to_nat(1);
                                                    v___x_3748_ =
                                                        lean_nat_sub(v_nargs_3745_, v___x_3747_);
                                                    leanh::lean_dec(v_nargs_3745_);
                                                    leanh::lean_inc_n(v_a_3726_, 2);
                                                    v___x_3749_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3726_, v___x_3746_, v___x_3748_);
                                                    v___x_3750_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3750_,
                                                        0,
                                                        v_snd_3707_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3750_,
                                                        1,
                                                        v___x_3743_,
                                                    );
                                                    v___x_3751_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3751_,
                                                        0,
                                                        v_fst_3706_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3751_,
                                                        1,
                                                        v___x_3750_,
                                                    );
                                                    v_sz_3752_ = lean_array_size(v___x_3749_);
                                                    v___x_3753_ = 0usize;
                                                    leanh::lean_inc_ref(v_ctx_3684_);
                                                    v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_3726_, v_ctx_3684_, v___x_3738_, v___x_3749_, v_sz_3752_, v___x_3753_, v___x_3751_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
                                                    leanh::lean_dec_ref(v___x_3749_);
                                                    if leanh::lean_obj_tag(v___x_3754_) == 0
                                                    {
                                                        v_a_3755_ = leanh::lean_ctor_get(
                                                            v___x_3754_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_3755_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_3754_,
                                                            1,
                                                        );
                                                        v_snd_3756_ = leanh::lean_ctor_get(
                                                            v_a_3755_, 1,
                                                        );
                                                        leanh::lean_inc(v_snd_3756_);
                                                        v_fst_3757_ = leanh::lean_ctor_get(
                                                            v_a_3755_, 0,
                                                        );
                                                        leanh::lean_inc(v_fst_3757_);
                                                        leanh::lean_dec(v_a_3755_);
                                                        v_fst_3758_ = leanh::lean_ctor_get(
                                                            v_snd_3756_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3765_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v_snd_3756_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3765_ == 0 {
                                                            v_unused_3766_ =
                                                                leanh::lean_ctor_get(
                                                                    v_snd_3756_,
                                                                    1,
                                                                );
                                                            leanh::lean_dec(v_unused_3766_);
                                                            v___x_3760_ = v_snd_3756_;
                                                            v_isShared_3761_ =
                                                                v_isSharedCheck_3765_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_fst_3758_);
                                                            leanh::lean_dec(v_snd_3756_);
                                                            v___x_3760_ = leanh::lean_box(0);
                                                            v_isShared_3761_ =
                                                                v_isSharedCheck_3765_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_del_object(v___x_3709_);
                                                        leanh::lean_dec_ref(v_ctx_3684_);
                                                        v_a_3767_ = leanh::lean_ctor_get(
                                                            v___x_3754_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3774_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_3754_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3774_ == 0 {
                                                            v___x_3769_ = v___x_3754_;
                                                            v_isShared_3770_ =
                                                                v_isSharedCheck_3774_;
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_3767_);
                                                            leanh::lean_dec(v___x_3754_);
                                                            v___x_3769_ = leanh::lean_box(0);
                                                            v_isShared_3770_ =
                                                                v_isSharedCheck_3774_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_3738_);
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_3738_);
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_3738_);
                                            leanh::lean_del_object(v___x_3709_);
                                            leanh::lean_dec(v_snd_3707_);
                                            leanh::lean_dec(v_fst_3706_);
                                            leanh::lean_dec_ref(v_ctx_3684_);
                                            v_a_3775_ = leanh::lean_ctor_get(v___x_3739_, 0);
                                            v_isSharedCheck_3782_ =
                                                (!leanh::lean_is_exclusive(v___x_3739_))
                                                    as u8;
                                            if v_isSharedCheck_3782_ == 0 {
                                                v___x_3777_ = v___x_3739_;
                                                v_isShared_3778_ = v_isSharedCheck_3782_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3775_);
                                                leanh::lean_dec(v___x_3739_);
                                                v___x_3777_ = leanh::lean_box(0);
                                                v_isShared_3778_ = v_isSharedCheck_3782_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_3783_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3783_, 0, v_fst_3706_);
                                        leanh::lean_ctor_set(v___x_3783_, 1, v_snd_3707_);
                                        v_a_3713_ = v___x_3783_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_3709_);
                                    leanh::lean_dec(v_snd_3707_);
                                    leanh::lean_dec(v_fst_3706_);
                                    leanh::lean_dec_ref(v_ctx_3684_);
                                    v_a_3784_ = leanh::lean_ctor_get(v___x_3735_, 0);
                                    v_isSharedCheck_3791_ =
                                        (!leanh::lean_is_exclusive(v___x_3735_)) as u8;
                                    if v_isSharedCheck_3791_ == 0 {
                                        v___x_3786_ = v___x_3735_;
                                        v_isShared_3787_ = v_isSharedCheck_3791_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3784_);
                                        leanh::lean_dec(v___x_3735_);
                                        v___x_3786_ = leanh::lean_box(0);
                                        v_isShared_3787_ = v_isSharedCheck_3791_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_3709_);
                            leanh::lean_dec(v_snd_3707_);
                            leanh::lean_dec(v_fst_3706_);
                            leanh::lean_dec_ref(v_ctx_3684_);
                            v_a_3792_ = leanh::lean_ctor_get(v___x_3730_, 0);
                            v_isSharedCheck_3799_ =
                                (!leanh::lean_is_exclusive(v___x_3730_)) as u8;
                            if v_isSharedCheck_3799_ == 0 {
                                v___x_3794_ = v___x_3730_;
                                v_isShared_3795_ = v_isSharedCheck_3799_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3792_);
                                leanh::lean_dec(v___x_3730_);
                                v___x_3794_ = leanh::lean_box(0);
                                v_isShared_3795_ = v_isSharedCheck_3799_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3761_ == 0 {
                    leanh::lean_ctor_set(v___x_3760_, 1, v_fst_3758_);
                    leanh::lean_ctor_set(v___x_3760_, 0, v_fst_3757_);
                    v___x_3763_ = v___x_3760_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3764_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_fst_3757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_fst_3758_);
                    v___x_3763_ = v_reuseFailAlloc_3764_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_3713_ = v___x_3763_;
                state = 3;
                continue;
            }
            11 => {
                if v_isShared_3770_ == 0 {
                    v___x_3772_ = v___x_3769_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3773_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
                    v___x_3772_ = v_reuseFailAlloc_3773_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3772_;
            }
            13 => {
                if v_isShared_3778_ == 0 {
                    v___x_3780_ = v___x_3777_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3781_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
                    v___x_3780_ = v_reuseFailAlloc_3781_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3780_;
            }
            15 => {
                if v_isShared_3787_ == 0 {
                    v___x_3789_ = v___x_3786_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3790_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
                    v___x_3789_ = v_reuseFailAlloc_3790_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3789_;
            }
            17 => {
                if v_isShared_3795_ == 0 {
                    v___x_3797_ = v___x_3794_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3798_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
                    v___x_3797_ = v_reuseFailAlloc_3798_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15___boxed(
    mut v_ctx_3805_: *mut leanh::LeanObject,
    mut v_as_3806_: *mut leanh::LeanObject,
    mut v_sz_3807_: *mut leanh::LeanObject,
    mut v_i_3808_: *mut leanh::LeanObject,
    mut v_b_3809_: *mut leanh::LeanObject,
    mut v___y_3810_: *mut leanh::LeanObject,
    mut v___y_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
    mut v___y_3813_: *mut leanh::LeanObject,
    mut v___y_3814_: *mut leanh::LeanObject,
    mut v___y_3815_: *mut leanh::LeanObject,
    mut v___y_3816_: *mut leanh::LeanObject,
    mut v___y_3817_: *mut leanh::LeanObject,
    mut v___y_3818_: *mut leanh::LeanObject,
    mut v___y_3819_: *mut leanh::LeanObject,
    mut v___y_3820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3821_: usize = 0;
    let mut v_i_boxed_3822_: usize = 0;
    let mut v_res_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3821_ = leanh::lean_unbox_usize(v_sz_3807_);
    leanh::lean_dec(v_sz_3807_);
    v_i_boxed_3822_ = leanh::lean_unbox_usize(v_i_3808_);
    leanh::lean_dec(v_i_3808_);
    v_res_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_3805_, v_as_3806_, v_sz_boxed_3821_, v_i_boxed_3822_, v_b_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
    leanh::lean_dec(v___y_3819_);
    leanh::lean_dec_ref(v___y_3818_);
    leanh::lean_dec(v___y_3817_);
    leanh::lean_dec_ref(v___y_3816_);
    leanh::lean_dec(v___y_3815_);
    leanh::lean_dec_ref(v___y_3814_);
    leanh::lean_dec(v___y_3813_);
    leanh::lean_dec_ref(v___y_3812_);
    leanh::lean_dec(v___y_3811_);
    leanh::lean_dec(v___y_3810_);
    leanh::lean_dec_ref(v_as_3806_);
    return v_res_3823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(
    mut v_ctx_3824_: *mut leanh::LeanObject,
    mut v_as_3825_: *mut leanh::LeanObject,
    mut v_sz_3826_: usize,
    mut v_i_3827_: usize,
    mut v_b_3828_: *mut leanh::LeanObject,
    mut v___y_3829_: *mut leanh::LeanObject,
    mut v___y_3830_: *mut leanh::LeanObject,
    mut v___y_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
    mut v___y_3837_: *mut leanh::LeanObject,
    mut v___y_3838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3840_: u8 = 0;
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3845_: u8 = 0;
    let mut v_fst_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: usize = 0;
    let mut v___x_3857_: usize = 0;
    let mut v_reuseFailAlloc_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: u8 = 0;
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: u8 = 0;
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInterpreted_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: u8 = 0;
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3882_: u8 = 0;
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3892_: usize = 0;
    let mut v___x_3893_: usize = 0;
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_unused_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3910_: u8 = 0;
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3914_: u8 = 0;
    let mut v_a_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3922_: u8 = 0;
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3927_: u8 = 0;
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v_a_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3935_: u8 = 0;
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3939_: u8 = 0;
    let mut v___x_3940_: u8 = 0;
    let mut v___x_3941_: u8 = 0;
    let mut v_isSharedCheck_3942_: u8 = 0;
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_unused_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3840_ = lean_usize_dec_lt(v_i_3827_, v_sz_3826_);
                if v___x_3840_ == 0 {
                    leanh::lean_dec_ref(v_ctx_3824_);
                    v___x_3841_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3841_, 0, v_b_3828_);
                    return v___x_3841_;
                } else {
                    v_snd_3842_ = leanh::lean_ctor_get(v_b_3828_, 1);
                    v_isSharedCheck_3943_ = (!leanh::lean_is_exclusive(v_b_3828_)) as u8;
                    if v_isSharedCheck_3943_ == 0 {
                        v_unused_3944_ = leanh::lean_ctor_get(v_b_3828_, 0);
                        leanh::lean_dec(v_unused_3944_);
                        v___x_3844_ = v_b_3828_;
                        v_isShared_3845_ = v_isSharedCheck_3943_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3842_);
                        leanh::lean_dec(v_b_3828_);
                        v___x_3844_ = leanh::lean_box(0);
                        v_isShared_3845_ = v_isSharedCheck_3943_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3846_ = leanh::lean_ctor_get(v_snd_3842_, 0);
                v_snd_3847_ = leanh::lean_ctor_get(v_snd_3842_, 1);
                v_isSharedCheck_3942_ = (!leanh::lean_is_exclusive(v_snd_3842_)) as u8;
                if v_isSharedCheck_3942_ == 0 {
                    v___x_3849_ = v_snd_3842_;
                    v_isShared_3850_ = v_isSharedCheck_3942_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3847_);
                    leanh::lean_inc(v_fst_3846_);
                    leanh::lean_dec(v_snd_3842_);
                    v___x_3849_ = leanh::lean_box(0);
                    v_isShared_3850_ = v_isSharedCheck_3942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3851_ = leanh::lean_box(0);
                v_a_3866_ = lean_array_uget_borrowed(v_as_3825_, v_i_3827_);
                v___x_3940_ = l_Lean_Expr_isApp(v_a_3866_);
                if v___x_3940_ == 0 {
                    v___y_3868_ = v___x_3940_;
                    state = 8;
                    continue;
                } else {
                    v___x_3941_ = l_Lean_Expr_isEq(v_a_3866_);
                    if v___x_3941_ == 0 {
                        v___y_3868_ = v___x_3940_;
                        state = 8;
                        continue;
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3850_ == 0 {
                    leanh::lean_ctor_set(v___x_3849_, 1, v_a_3853_);
                    leanh::lean_ctor_set(v___x_3849_, 0, v___x_3851_);
                    v___x_3855_ = v___x_3849_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3859_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3851_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 1, v_a_3853_);
                    v___x_3855_ = v_reuseFailAlloc_3859_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3856_ = 1usize;
                v___x_3857_ = lean_usize_add(v_i_3827_, v___x_3856_);
                v_i_3827_ = v___x_3857_;
                v_b_3828_ = v___x_3855_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_3845_ == 0 {
                    leanh::lean_ctor_set(v___x_3844_, 1, v_snd_3847_);
                    leanh::lean_ctor_set(v___x_3844_, 0, v_fst_3846_);
                    v___x_3862_ = v___x_3844_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3863_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_fst_3846_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_snd_3847_);
                    v___x_3862_ = v_reuseFailAlloc_3863_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_3853_ = v___x_3862_;
                state = 3;
                continue;
            }
            7 => {
                v___x_3865_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3865_, 0, v_fst_3846_);
                leanh::lean_ctor_set(v___x_3865_, 1, v_snd_3847_);
                v_a_3853_ = v___x_3865_;
                state = 3;
                continue;
            }
            8 => {
                if v___y_3868_ == 0 {
                    state = 5;
                    continue;
                } else {
                    v___x_3869_ = l_Lean_Expr_isHEq(v_a_3866_);
                    if v___x_3869_ == 0 {
                        leanh::lean_del_object(v___x_3844_);
                        leanh::lean_inc(v_a_3866_);
                        v___x_3870_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                            v_a_3866_,
                            v___y_3829_,
                            v___y_3835_,
                            v___y_3836_,
                            v___y_3837_,
                            v___y_3838_,
                        );
                        if leanh::lean_obj_tag(v___x_3870_) == 0 {
                            v_a_3871_ = leanh::lean_ctor_get(v___x_3870_, 0);
                            leanh::lean_inc(v_a_3871_);
                            leanh::lean_dec_ref_known(v___x_3870_, 1);
                            v___x_3872_ = (leanh::lean_unbox(v_a_3871_) as u8);
                            leanh::lean_dec(v_a_3871_);
                            if v___x_3872_ == 0 {
                                v___x_3873_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3873_, 0, v_fst_3846_);
                                leanh::lean_ctor_set(v___x_3873_, 1, v_snd_3847_);
                                v_a_3853_ = v___x_3873_;
                                state = 3;
                                continue;
                            } else {
                                v_isInterpreted_3874_ = leanh::lean_ctor_get(v_ctx_3824_, 0);
                                leanh::lean_inc_ref(v_isInterpreted_3874_);
                                leanh::lean_inc(v___y_3838_);
                                leanh::lean_inc_ref(v___y_3837_);
                                leanh::lean_inc(v___y_3836_);
                                leanh::lean_inc_ref(v___y_3835_);
                                leanh::lean_inc(v___y_3834_);
                                leanh::lean_inc_ref(v___y_3833_);
                                leanh::lean_inc(v___y_3832_);
                                leanh::lean_inc_ref(v___y_3831_);
                                leanh::lean_inc(v___y_3830_);
                                leanh::lean_inc(v___y_3829_);
                                leanh::lean_inc(v_a_3866_);
                                v___x_3875_ = leanh::lean_apply_12(
                                    v_isInterpreted_3874_,
                                    v_a_3866_,
                                    v___y_3829_,
                                    v___y_3830_,
                                    v___y_3831_,
                                    v___y_3832_,
                                    v___y_3833_,
                                    v___y_3834_,
                                    v___y_3835_,
                                    v___y_3836_,
                                    v___y_3837_,
                                    v___y_3838_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_3875_) == 0 {
                                    v_a_3876_ = leanh::lean_ctor_get(v___x_3875_, 0);
                                    leanh::lean_inc(v_a_3876_);
                                    leanh::lean_dec_ref_known(v___x_3875_, 1);
                                    v___x_3877_ = (leanh::lean_unbox(v_a_3876_) as u8);
                                    leanh::lean_dec(v_a_3876_);
                                    if v___x_3877_ == 0 {
                                        v___x_3878_ = l_Lean_Expr_getAppFn(v_a_3866_);
                                        leanh::lean_inc_ref(v___x_3878_);
                                        v___x_3879_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_3878_, v___y_3837_, v___y_3838_);
                                        if leanh::lean_obj_tag(v___x_3879_) == 0 {
                                            v_a_3880_ = leanh::lean_ctor_get(v___x_3879_, 0);
                                            leanh::lean_inc(v_a_3880_);
                                            leanh::lean_dec_ref_known(v___x_3879_, 1);
                                            v___x_3881_ =
                                                (leanh::lean_unbox(v_a_3880_) as u8);
                                            leanh::lean_dec(v_a_3880_);
                                            if v___x_3881_ == 0 {
                                                v___x_3882_ =
                                                    l_Lean_Meta_Grind_isCastLikeFn(v___x_3878_);
                                                if v___x_3882_ == 0 {
                                                    v___x_3883_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v_dummy_3884_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
                                                    v_nargs_3885_ =
                                                        l_Lean_Expr_getAppNumArgs(v_a_3866_);
                                                    leanh::lean_inc(v_nargs_3885_);
                                                    v___x_3886_ =
                                                        lean_mk_array(v_nargs_3885_, v_dummy_3884_);
                                                    v___x_3887_ =
                                                        leanh::lean_unsigned_to_nat(1);
                                                    v___x_3888_ =
                                                        lean_nat_sub(v_nargs_3885_, v___x_3887_);
                                                    leanh::lean_dec(v_nargs_3885_);
                                                    leanh::lean_inc_n(v_a_3866_, 2);
                                                    v___x_3889_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3866_, v___x_3886_, v___x_3888_);
                                                    v___x_3890_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3890_,
                                                        0,
                                                        v_snd_3847_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3890_,
                                                        1,
                                                        v___x_3883_,
                                                    );
                                                    v___x_3891_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3891_,
                                                        0,
                                                        v_fst_3846_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3891_,
                                                        1,
                                                        v___x_3890_,
                                                    );
                                                    v_sz_3892_ = lean_array_size(v___x_3889_);
                                                    v___x_3893_ = 0usize;
                                                    leanh::lean_inc_ref(v_ctx_3824_);
                                                    v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_3866_, v_ctx_3824_, v___x_3878_, v___x_3889_, v_sz_3892_, v___x_3893_, v___x_3891_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
                                                    leanh::lean_dec_ref(v___x_3889_);
                                                    if leanh::lean_obj_tag(v___x_3894_) == 0
                                                    {
                                                        v_a_3895_ = leanh::lean_ctor_get(
                                                            v___x_3894_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_3895_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_3894_,
                                                            1,
                                                        );
                                                        v_snd_3896_ = leanh::lean_ctor_get(
                                                            v_a_3895_, 1,
                                                        );
                                                        leanh::lean_inc(v_snd_3896_);
                                                        v_fst_3897_ = leanh::lean_ctor_get(
                                                            v_a_3895_, 0,
                                                        );
                                                        leanh::lean_inc(v_fst_3897_);
                                                        leanh::lean_dec(v_a_3895_);
                                                        v_fst_3898_ = leanh::lean_ctor_get(
                                                            v_snd_3896_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3905_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v_snd_3896_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3905_ == 0 {
                                                            v_unused_3906_ =
                                                                leanh::lean_ctor_get(
                                                                    v_snd_3896_,
                                                                    1,
                                                                );
                                                            leanh::lean_dec(v_unused_3906_);
                                                            v___x_3900_ = v_snd_3896_;
                                                            v_isShared_3901_ =
                                                                v_isSharedCheck_3905_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_fst_3898_);
                                                            leanh::lean_dec(v_snd_3896_);
                                                            v___x_3900_ = leanh::lean_box(0);
                                                            v_isShared_3901_ =
                                                                v_isSharedCheck_3905_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_del_object(v___x_3849_);
                                                        leanh::lean_dec_ref(v_ctx_3824_);
                                                        v_a_3907_ = leanh::lean_ctor_get(
                                                            v___x_3894_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3914_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_3894_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3914_ == 0 {
                                                            v___x_3909_ = v___x_3894_;
                                                            v_isShared_3910_ =
                                                                v_isSharedCheck_3914_;
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_3907_);
                                                            leanh::lean_dec(v___x_3894_);
                                                            v___x_3909_ = leanh::lean_box(0);
                                                            v_isShared_3910_ =
                                                                v_isSharedCheck_3914_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_3878_);
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_3878_);
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_3878_);
                                            leanh::lean_del_object(v___x_3849_);
                                            leanh::lean_dec(v_snd_3847_);
                                            leanh::lean_dec(v_fst_3846_);
                                            leanh::lean_dec_ref(v_ctx_3824_);
                                            v_a_3915_ = leanh::lean_ctor_get(v___x_3879_, 0);
                                            v_isSharedCheck_3922_ =
                                                (!leanh::lean_is_exclusive(v___x_3879_))
                                                    as u8;
                                            if v_isSharedCheck_3922_ == 0 {
                                                v___x_3917_ = v___x_3879_;
                                                v_isShared_3918_ = v_isSharedCheck_3922_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3915_);
                                                leanh::lean_dec(v___x_3879_);
                                                v___x_3917_ = leanh::lean_box(0);
                                                v_isShared_3918_ = v_isSharedCheck_3922_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_3923_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3923_, 0, v_fst_3846_);
                                        leanh::lean_ctor_set(v___x_3923_, 1, v_snd_3847_);
                                        v_a_3853_ = v___x_3923_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_3849_);
                                    leanh::lean_dec(v_snd_3847_);
                                    leanh::lean_dec(v_fst_3846_);
                                    leanh::lean_dec_ref(v_ctx_3824_);
                                    v_a_3924_ = leanh::lean_ctor_get(v___x_3875_, 0);
                                    v_isSharedCheck_3931_ =
                                        (!leanh::lean_is_exclusive(v___x_3875_)) as u8;
                                    if v_isSharedCheck_3931_ == 0 {
                                        v___x_3926_ = v___x_3875_;
                                        v_isShared_3927_ = v_isSharedCheck_3931_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3924_);
                                        leanh::lean_dec(v___x_3875_);
                                        v___x_3926_ = leanh::lean_box(0);
                                        v_isShared_3927_ = v_isSharedCheck_3931_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_3849_);
                            leanh::lean_dec(v_snd_3847_);
                            leanh::lean_dec(v_fst_3846_);
                            leanh::lean_dec_ref(v_ctx_3824_);
                            v_a_3932_ = leanh::lean_ctor_get(v___x_3870_, 0);
                            v_isSharedCheck_3939_ =
                                (!leanh::lean_is_exclusive(v___x_3870_)) as u8;
                            if v_isSharedCheck_3939_ == 0 {
                                v___x_3934_ = v___x_3870_;
                                v_isShared_3935_ = v_isSharedCheck_3939_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3932_);
                                leanh::lean_dec(v___x_3870_);
                                v___x_3934_ = leanh::lean_box(0);
                                v_isShared_3935_ = v_isSharedCheck_3939_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3901_ == 0 {
                    leanh::lean_ctor_set(v___x_3900_, 1, v_fst_3898_);
                    leanh::lean_ctor_set(v___x_3900_, 0, v_fst_3897_);
                    v___x_3903_ = v___x_3900_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_fst_3897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_fst_3898_);
                    v___x_3903_ = v_reuseFailAlloc_3904_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_3853_ = v___x_3903_;
                state = 3;
                continue;
            }
            11 => {
                if v_isShared_3910_ == 0 {
                    v___x_3912_ = v___x_3909_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3913_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
                    v___x_3912_ = v_reuseFailAlloc_3913_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3912_;
            }
            13 => {
                if v_isShared_3918_ == 0 {
                    v___x_3920_ = v___x_3917_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3921_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
                    v___x_3920_ = v_reuseFailAlloc_3921_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3920_;
            }
            15 => {
                if v_isShared_3927_ == 0 {
                    v___x_3929_ = v___x_3926_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
                    v___x_3929_ = v_reuseFailAlloc_3930_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3929_;
            }
            17 => {
                if v_isShared_3935_ == 0 {
                    v___x_3937_ = v___x_3934_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3938_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
                    v___x_3937_ = v_reuseFailAlloc_3938_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3937_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26___boxed(
    mut v_ctx_3945_: *mut leanh::LeanObject,
    mut v_as_3946_: *mut leanh::LeanObject,
    mut v_sz_3947_: *mut leanh::LeanObject,
    mut v_i_3948_: *mut leanh::LeanObject,
    mut v_b_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
    mut v___y_3956_: *mut leanh::LeanObject,
    mut v___y_3957_: *mut leanh::LeanObject,
    mut v___y_3958_: *mut leanh::LeanObject,
    mut v___y_3959_: *mut leanh::LeanObject,
    mut v___y_3960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3961_: usize = 0;
    let mut v_i_boxed_3962_: usize = 0;
    let mut v_res_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3961_ = leanh::lean_unbox_usize(v_sz_3947_);
    leanh::lean_dec(v_sz_3947_);
    v_i_boxed_3962_ = leanh::lean_unbox_usize(v_i_3948_);
    leanh::lean_dec(v_i_3948_);
    v_res_3963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_3945_, v_as_3946_, v_sz_boxed_3961_, v_i_boxed_3962_, v_b_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
    leanh::lean_dec(v___y_3959_);
    leanh::lean_dec_ref(v___y_3958_);
    leanh::lean_dec(v___y_3957_);
    leanh::lean_dec_ref(v___y_3956_);
    leanh::lean_dec(v___y_3955_);
    leanh::lean_dec_ref(v___y_3954_);
    leanh::lean_dec(v___y_3953_);
    leanh::lean_dec_ref(v___y_3952_);
    leanh::lean_dec(v___y_3951_);
    leanh::lean_dec(v___y_3950_);
    leanh::lean_dec_ref(v_as_3946_);
    return v_res_3963_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(
    mut v_ctx_3964_: *mut leanh::LeanObject,
    mut v_as_3965_: *mut leanh::LeanObject,
    mut v_sz_3966_: usize,
    mut v_i_3967_: usize,
    mut v_b_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
    mut v___y_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
    mut v___y_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3980_: u8 = 0;
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3985_: u8 = 0;
    let mut v_fst_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: usize = 0;
    let mut v___x_3997_: usize = 0;
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4008_: u8 = 0;
    let mut v___x_4009_: u8 = 0;
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: u8 = 0;
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInterpreted_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4032_: usize = 0;
    let mut v___x_4033_: usize = 0;
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut v_unused_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4050_: u8 = 0;
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4054_: u8 = 0;
    let mut v_a_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4058_: u8 = 0;
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4062_: u8 = 0;
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4067_: u8 = 0;
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut v_a_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4075_: u8 = 0;
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4079_: u8 = 0;
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: u8 = 0;
    let mut v_isSharedCheck_4082_: u8 = 0;
    let mut v_isSharedCheck_4083_: u8 = 0;
    let mut v_unused_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3980_ = lean_usize_dec_lt(v_i_3967_, v_sz_3966_);
                if v___x_3980_ == 0 {
                    leanh::lean_dec_ref(v_ctx_3964_);
                    v___x_3981_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3981_, 0, v_b_3968_);
                    return v___x_3981_;
                } else {
                    v_snd_3982_ = leanh::lean_ctor_get(v_b_3968_, 1);
                    v_isSharedCheck_4083_ = (!leanh::lean_is_exclusive(v_b_3968_)) as u8;
                    if v_isSharedCheck_4083_ == 0 {
                        v_unused_4084_ = leanh::lean_ctor_get(v_b_3968_, 0);
                        leanh::lean_dec(v_unused_4084_);
                        v___x_3984_ = v_b_3968_;
                        v_isShared_3985_ = v_isSharedCheck_4083_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3982_);
                        leanh::lean_dec(v_b_3968_);
                        v___x_3984_ = leanh::lean_box(0);
                        v_isShared_3985_ = v_isSharedCheck_4083_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3986_ = leanh::lean_ctor_get(v_snd_3982_, 0);
                v_snd_3987_ = leanh::lean_ctor_get(v_snd_3982_, 1);
                v_isSharedCheck_4082_ = (!leanh::lean_is_exclusive(v_snd_3982_)) as u8;
                if v_isSharedCheck_4082_ == 0 {
                    v___x_3989_ = v_snd_3982_;
                    v_isShared_3990_ = v_isSharedCheck_4082_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3987_);
                    leanh::lean_inc(v_fst_3986_);
                    leanh::lean_dec(v_snd_3982_);
                    v___x_3989_ = leanh::lean_box(0);
                    v_isShared_3990_ = v_isSharedCheck_4082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3991_ = leanh::lean_box(0);
                v_a_4006_ = lean_array_uget_borrowed(v_as_3965_, v_i_3967_);
                v___x_4080_ = l_Lean_Expr_isApp(v_a_4006_);
                if v___x_4080_ == 0 {
                    v___y_4008_ = v___x_4080_;
                    state = 8;
                    continue;
                } else {
                    v___x_4081_ = l_Lean_Expr_isEq(v_a_4006_);
                    if v___x_4081_ == 0 {
                        v___y_4008_ = v___x_4080_;
                        state = 8;
                        continue;
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3990_ == 0 {
                    leanh::lean_ctor_set(v___x_3989_, 1, v_a_3993_);
                    leanh::lean_ctor_set(v___x_3989_, 0, v___x_3991_);
                    v___x_3995_ = v___x_3989_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3999_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3991_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_a_3993_);
                    v___x_3995_ = v_reuseFailAlloc_3999_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3996_ = 1usize;
                v___x_3997_ = lean_usize_add(v_i_3967_, v___x_3996_);
                v___x_3998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_3964_, v_as_3965_, v_sz_3966_, v___x_3997_, v___x_3995_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
                return v___x_3998_;
            }
            5 => {
                if v_isShared_3985_ == 0 {
                    leanh::lean_ctor_set(v___x_3984_, 1, v_snd_3987_);
                    leanh::lean_ctor_set(v___x_3984_, 0, v_fst_3986_);
                    v___x_4002_ = v___x_3984_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4003_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_fst_3986_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_snd_3987_);
                    v___x_4002_ = v_reuseFailAlloc_4003_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_3993_ = v___x_4002_;
                state = 3;
                continue;
            }
            7 => {
                v___x_4005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4005_, 0, v_fst_3986_);
                leanh::lean_ctor_set(v___x_4005_, 1, v_snd_3987_);
                v_a_3993_ = v___x_4005_;
                state = 3;
                continue;
            }
            8 => {
                if v___y_4008_ == 0 {
                    state = 5;
                    continue;
                } else {
                    v___x_4009_ = l_Lean_Expr_isHEq(v_a_4006_);
                    if v___x_4009_ == 0 {
                        leanh::lean_del_object(v___x_3984_);
                        leanh::lean_inc(v_a_4006_);
                        v___x_4010_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                            v_a_4006_,
                            v___y_3969_,
                            v___y_3975_,
                            v___y_3976_,
                            v___y_3977_,
                            v___y_3978_,
                        );
                        if leanh::lean_obj_tag(v___x_4010_) == 0 {
                            v_a_4011_ = leanh::lean_ctor_get(v___x_4010_, 0);
                            leanh::lean_inc(v_a_4011_);
                            leanh::lean_dec_ref_known(v___x_4010_, 1);
                            v___x_4012_ = (leanh::lean_unbox(v_a_4011_) as u8);
                            leanh::lean_dec(v_a_4011_);
                            if v___x_4012_ == 0 {
                                v___x_4013_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4013_, 0, v_fst_3986_);
                                leanh::lean_ctor_set(v___x_4013_, 1, v_snd_3987_);
                                v_a_3993_ = v___x_4013_;
                                state = 3;
                                continue;
                            } else {
                                v_isInterpreted_4014_ = leanh::lean_ctor_get(v_ctx_3964_, 0);
                                leanh::lean_inc_ref(v_isInterpreted_4014_);
                                leanh::lean_inc(v___y_3978_);
                                leanh::lean_inc_ref(v___y_3977_);
                                leanh::lean_inc(v___y_3976_);
                                leanh::lean_inc_ref(v___y_3975_);
                                leanh::lean_inc(v___y_3974_);
                                leanh::lean_inc_ref(v___y_3973_);
                                leanh::lean_inc(v___y_3972_);
                                leanh::lean_inc_ref(v___y_3971_);
                                leanh::lean_inc(v___y_3970_);
                                leanh::lean_inc(v___y_3969_);
                                leanh::lean_inc(v_a_4006_);
                                v___x_4015_ = leanh::lean_apply_12(
                                    v_isInterpreted_4014_,
                                    v_a_4006_,
                                    v___y_3969_,
                                    v___y_3970_,
                                    v___y_3971_,
                                    v___y_3972_,
                                    v___y_3973_,
                                    v___y_3974_,
                                    v___y_3975_,
                                    v___y_3976_,
                                    v___y_3977_,
                                    v___y_3978_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_4015_) == 0 {
                                    v_a_4016_ = leanh::lean_ctor_get(v___x_4015_, 0);
                                    leanh::lean_inc(v_a_4016_);
                                    leanh::lean_dec_ref_known(v___x_4015_, 1);
                                    v___x_4017_ = (leanh::lean_unbox(v_a_4016_) as u8);
                                    leanh::lean_dec(v_a_4016_);
                                    if v___x_4017_ == 0 {
                                        v___x_4018_ = l_Lean_Expr_getAppFn(v_a_4006_);
                                        leanh::lean_inc_ref(v___x_4018_);
                                        v___x_4019_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_4018_, v___y_3977_, v___y_3978_);
                                        if leanh::lean_obj_tag(v___x_4019_) == 0 {
                                            v_a_4020_ = leanh::lean_ctor_get(v___x_4019_, 0);
                                            leanh::lean_inc(v_a_4020_);
                                            leanh::lean_dec_ref_known(v___x_4019_, 1);
                                            v___x_4021_ =
                                                (leanh::lean_unbox(v_a_4020_) as u8);
                                            leanh::lean_dec(v_a_4020_);
                                            if v___x_4021_ == 0 {
                                                v___x_4022_ =
                                                    l_Lean_Meta_Grind_isCastLikeFn(v___x_4018_);
                                                if v___x_4022_ == 0 {
                                                    v___x_4023_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v_dummy_4024_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
                                                    v_nargs_4025_ =
                                                        l_Lean_Expr_getAppNumArgs(v_a_4006_);
                                                    leanh::lean_inc(v_nargs_4025_);
                                                    v___x_4026_ =
                                                        lean_mk_array(v_nargs_4025_, v_dummy_4024_);
                                                    v___x_4027_ =
                                                        leanh::lean_unsigned_to_nat(1);
                                                    v___x_4028_ =
                                                        lean_nat_sub(v_nargs_4025_, v___x_4027_);
                                                    leanh::lean_dec(v_nargs_4025_);
                                                    leanh::lean_inc_n(v_a_4006_, 2);
                                                    v___x_4029_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4006_, v___x_4026_, v___x_4028_);
                                                    v___x_4030_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_4030_,
                                                        0,
                                                        v_snd_3987_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_4030_,
                                                        1,
                                                        v___x_4023_,
                                                    );
                                                    v___x_4031_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_4031_,
                                                        0,
                                                        v_fst_3986_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_4031_,
                                                        1,
                                                        v___x_4030_,
                                                    );
                                                    v_sz_4032_ = lean_array_size(v___x_4029_);
                                                    v___x_4033_ = 0usize;
                                                    leanh::lean_inc_ref(v_ctx_3964_);
                                                    v___x_4034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_4006_, v_ctx_3964_, v___x_4018_, v___x_4029_, v_sz_4032_, v___x_4033_, v___x_4031_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
                                                    leanh::lean_dec_ref(v___x_4029_);
                                                    if leanh::lean_obj_tag(v___x_4034_) == 0
                                                    {
                                                        v_a_4035_ = leanh::lean_ctor_get(
                                                            v___x_4034_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_4035_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_4034_,
                                                            1,
                                                        );
                                                        v_snd_4036_ = leanh::lean_ctor_get(
                                                            v_a_4035_, 1,
                                                        );
                                                        leanh::lean_inc(v_snd_4036_);
                                                        v_fst_4037_ = leanh::lean_ctor_get(
                                                            v_a_4035_, 0,
                                                        );
                                                        leanh::lean_inc(v_fst_4037_);
                                                        leanh::lean_dec(v_a_4035_);
                                                        v_fst_4038_ = leanh::lean_ctor_get(
                                                            v_snd_4036_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4045_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v_snd_4036_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4045_ == 0 {
                                                            v_unused_4046_ =
                                                                leanh::lean_ctor_get(
                                                                    v_snd_4036_,
                                                                    1,
                                                                );
                                                            leanh::lean_dec(v_unused_4046_);
                                                            v___x_4040_ = v_snd_4036_;
                                                            v_isShared_4041_ =
                                                                v_isSharedCheck_4045_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_fst_4038_);
                                                            leanh::lean_dec(v_snd_4036_);
                                                            v___x_4040_ = leanh::lean_box(0);
                                                            v_isShared_4041_ =
                                                                v_isSharedCheck_4045_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_del_object(v___x_3989_);
                                                        leanh::lean_dec_ref(v_ctx_3964_);
                                                        v_a_4047_ = leanh::lean_ctor_get(
                                                            v___x_4034_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4054_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_4034_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4054_ == 0 {
                                                            v___x_4049_ = v___x_4034_;
                                                            v_isShared_4050_ =
                                                                v_isSharedCheck_4054_;
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_4047_);
                                                            leanh::lean_dec(v___x_4034_);
                                                            v___x_4049_ = leanh::lean_box(0);
                                                            v_isShared_4050_ =
                                                                v_isSharedCheck_4054_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_4018_);
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_4018_);
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_4018_);
                                            leanh::lean_del_object(v___x_3989_);
                                            leanh::lean_dec(v_snd_3987_);
                                            leanh::lean_dec(v_fst_3986_);
                                            leanh::lean_dec_ref(v_ctx_3964_);
                                            v_a_4055_ = leanh::lean_ctor_get(v___x_4019_, 0);
                                            v_isSharedCheck_4062_ =
                                                (!leanh::lean_is_exclusive(v___x_4019_))
                                                    as u8;
                                            if v_isSharedCheck_4062_ == 0 {
                                                v___x_4057_ = v___x_4019_;
                                                v_isShared_4058_ = v_isSharedCheck_4062_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4055_);
                                                leanh::lean_dec(v___x_4019_);
                                                v___x_4057_ = leanh::lean_box(0);
                                                v_isShared_4058_ = v_isSharedCheck_4062_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_4063_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4063_, 0, v_fst_3986_);
                                        leanh::lean_ctor_set(v___x_4063_, 1, v_snd_3987_);
                                        v_a_3993_ = v___x_4063_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_3989_);
                                    leanh::lean_dec(v_snd_3987_);
                                    leanh::lean_dec(v_fst_3986_);
                                    leanh::lean_dec_ref(v_ctx_3964_);
                                    v_a_4064_ = leanh::lean_ctor_get(v___x_4015_, 0);
                                    v_isSharedCheck_4071_ =
                                        (!leanh::lean_is_exclusive(v___x_4015_)) as u8;
                                    if v_isSharedCheck_4071_ == 0 {
                                        v___x_4066_ = v___x_4015_;
                                        v_isShared_4067_ = v_isSharedCheck_4071_;
                                        state = 15;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4064_);
                                        leanh::lean_dec(v___x_4015_);
                                        v___x_4066_ = leanh::lean_box(0);
                                        v_isShared_4067_ = v_isSharedCheck_4071_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_3989_);
                            leanh::lean_dec(v_snd_3987_);
                            leanh::lean_dec(v_fst_3986_);
                            leanh::lean_dec_ref(v_ctx_3964_);
                            v_a_4072_ = leanh::lean_ctor_get(v___x_4010_, 0);
                            v_isSharedCheck_4079_ =
                                (!leanh::lean_is_exclusive(v___x_4010_)) as u8;
                            if v_isSharedCheck_4079_ == 0 {
                                v___x_4074_ = v___x_4010_;
                                v_isShared_4075_ = v_isSharedCheck_4079_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4072_);
                                leanh::lean_dec(v___x_4010_);
                                v___x_4074_ = leanh::lean_box(0);
                                v_isShared_4075_ = v_isSharedCheck_4079_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4041_ == 0 {
                    leanh::lean_ctor_set(v___x_4040_, 1, v_fst_4038_);
                    leanh::lean_ctor_set(v___x_4040_, 0, v_fst_4037_);
                    v___x_4043_ = v___x_4040_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_fst_4037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_fst_4038_);
                    v___x_4043_ = v_reuseFailAlloc_4044_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_3993_ = v___x_4043_;
                state = 3;
                continue;
            }
            11 => {
                if v_isShared_4050_ == 0 {
                    v___x_4052_ = v___x_4049_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4053_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
                    v___x_4052_ = v_reuseFailAlloc_4053_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4052_;
            }
            13 => {
                if v_isShared_4058_ == 0 {
                    v___x_4060_ = v___x_4057_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4061_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
                    v___x_4060_ = v_reuseFailAlloc_4061_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4060_;
            }
            15 => {
                if v_isShared_4067_ == 0 {
                    v___x_4069_ = v___x_4066_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
                    v___x_4069_ = v_reuseFailAlloc_4070_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4069_;
            }
            17 => {
                if v_isShared_4075_ == 0 {
                    v___x_4077_ = v___x_4074_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
                    v___x_4077_ = v_reuseFailAlloc_4078_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18___boxed(
    mut v_ctx_4085_: *mut leanh::LeanObject,
    mut v_as_4086_: *mut leanh::LeanObject,
    mut v_sz_4087_: *mut leanh::LeanObject,
    mut v_i_4088_: *mut leanh::LeanObject,
    mut v_b_4089_: *mut leanh::LeanObject,
    mut v___y_4090_: *mut leanh::LeanObject,
    mut v___y_4091_: *mut leanh::LeanObject,
    mut v___y_4092_: *mut leanh::LeanObject,
    mut v___y_4093_: *mut leanh::LeanObject,
    mut v___y_4094_: *mut leanh::LeanObject,
    mut v___y_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
    mut v___y_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4101_: usize = 0;
    let mut v_i_boxed_4102_: usize = 0;
    let mut v_res_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4101_ = leanh::lean_unbox_usize(v_sz_4087_);
    leanh::lean_dec(v_sz_4087_);
    v_i_boxed_4102_ = leanh::lean_unbox_usize(v_i_4088_);
    leanh::lean_dec(v_i_4088_);
    v_res_4103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_4085_, v_as_4086_, v_sz_boxed_4101_, v_i_boxed_4102_, v_b_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
    leanh::lean_dec(v___y_4099_);
    leanh::lean_dec_ref(v___y_4098_);
    leanh::lean_dec(v___y_4097_);
    leanh::lean_dec_ref(v___y_4096_);
    leanh::lean_dec(v___y_4095_);
    leanh::lean_dec_ref(v___y_4094_);
    leanh::lean_dec(v___y_4093_);
    leanh::lean_dec_ref(v___y_4092_);
    leanh::lean_dec(v___y_4091_);
    leanh::lean_dec(v___y_4090_);
    leanh::lean_dec_ref(v_as_4086_);
    return v_res_4103_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(
    mut v_init_4104_: *mut leanh::LeanObject,
    mut v_ctx_4105_: *mut leanh::LeanObject,
    mut v_n_4106_: *mut leanh::LeanObject,
    mut v_b_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
    mut v___y_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
    mut v___y_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
    mut v___y_4115_: *mut leanh::LeanObject,
    mut v___y_4116_: *mut leanh::LeanObject,
    mut v___y_4117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4122_: usize = 0;
    let mut v___x_4123_: usize = 0;
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v_fst_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut v_a_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4143_: u8 = 0;
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_vs_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4151_: usize = 0;
    let mut v___x_4152_: usize = 0;
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4157_: u8 = 0;
    let mut v_fst_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v_a_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4172_: u8 = 0;
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_4106_) == 0 {
                    v_cs_4119_ = leanh::lean_ctor_get(v_n_4106_, 0);
                    v___x_4120_ = leanh::lean_box(0);
                    v___x_4121_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4121_, 0, v___x_4120_);
                    leanh::lean_ctor_set(v___x_4121_, 1, v_b_4107_);
                    v_sz_4122_ = lean_array_size(v_cs_4119_);
                    v___x_4123_ = 0usize;
                    v___x_4124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_4104_, v_ctx_4105_, v_cs_4119_, v_sz_4122_, v___x_4123_, v___x_4121_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
                    if leanh::lean_obj_tag(v___x_4124_) == 0 {
                        v_a_4125_ = leanh::lean_ctor_get(v___x_4124_, 0);
                        v_isSharedCheck_4139_ =
                            (!leanh::lean_is_exclusive(v___x_4124_)) as u8;
                        if v_isSharedCheck_4139_ == 0 {
                            v___x_4127_ = v___x_4124_;
                            v_isShared_4128_ = v_isSharedCheck_4139_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4125_);
                            leanh::lean_dec(v___x_4124_);
                            v___x_4127_ = leanh::lean_box(0);
                            v_isShared_4128_ = v_isSharedCheck_4139_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4140_ = leanh::lean_ctor_get(v___x_4124_, 0);
                        v_isSharedCheck_4147_ =
                            (!leanh::lean_is_exclusive(v___x_4124_)) as u8;
                        if v_isSharedCheck_4147_ == 0 {
                            v___x_4142_ = v___x_4124_;
                            v_isShared_4143_ = v_isSharedCheck_4147_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4140_);
                            leanh::lean_dec(v___x_4124_);
                            v___x_4142_ = leanh::lean_box(0);
                            v_isShared_4143_ = v_isSharedCheck_4147_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4148_ = leanh::lean_ctor_get(v_n_4106_, 0);
                    v___x_4149_ = leanh::lean_box(0);
                    v___x_4150_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4150_, 0, v___x_4149_);
                    leanh::lean_ctor_set(v___x_4150_, 1, v_b_4107_);
                    v_sz_4151_ = lean_array_size(v_vs_4148_);
                    v___x_4152_ = 0usize;
                    v___x_4153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_4105_, v_vs_4148_, v_sz_4151_, v___x_4152_, v___x_4150_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
                    if leanh::lean_obj_tag(v___x_4153_) == 0 {
                        v_a_4154_ = leanh::lean_ctor_get(v___x_4153_, 0);
                        v_isSharedCheck_4168_ =
                            (!leanh::lean_is_exclusive(v___x_4153_)) as u8;
                        if v_isSharedCheck_4168_ == 0 {
                            v___x_4156_ = v___x_4153_;
                            v_isShared_4157_ = v_isSharedCheck_4168_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4154_);
                            leanh::lean_dec(v___x_4153_);
                            v___x_4156_ = leanh::lean_box(0);
                            v_isShared_4157_ = v_isSharedCheck_4168_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4169_ = leanh::lean_ctor_get(v___x_4153_, 0);
                        v_isSharedCheck_4176_ =
                            (!leanh::lean_is_exclusive(v___x_4153_)) as u8;
                        if v_isSharedCheck_4176_ == 0 {
                            v___x_4171_ = v___x_4153_;
                            v_isShared_4172_ = v_isSharedCheck_4176_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4169_);
                            leanh::lean_dec(v___x_4153_);
                            v___x_4171_ = leanh::lean_box(0);
                            v_isShared_4172_ = v_isSharedCheck_4176_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4129_ = leanh::lean_ctor_get(v_a_4125_, 0);
                if leanh::lean_obj_tag(v_fst_4129_) == 0 {
                    v_snd_4130_ = leanh::lean_ctor_get(v_a_4125_, 1);
                    leanh::lean_inc(v_snd_4130_);
                    leanh::lean_dec(v_a_4125_);
                    v___x_4131_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4131_, 0, v_snd_4130_);
                    if v_isShared_4128_ == 0 {
                        leanh::lean_ctor_set(v___x_4127_, 0, v___x_4131_);
                        v___x_4133_ = v___x_4127_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4134_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
                        v___x_4133_ = v_reuseFailAlloc_4134_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4129_);
                    leanh::lean_dec(v_a_4125_);
                    v_val_4135_ = leanh::lean_ctor_get(v_fst_4129_, 0);
                    leanh::lean_inc(v_val_4135_);
                    leanh::lean_dec_ref_known(v_fst_4129_, 1);
                    if v_isShared_4128_ == 0 {
                        leanh::lean_ctor_set(v___x_4127_, 0, v_val_4135_);
                        v___x_4137_ = v___x_4127_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4138_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_val_4135_);
                        v___x_4137_ = v_reuseFailAlloc_4138_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4133_;
            }
            3 => {
                return v___x_4137_;
            }
            4 => {
                if v_isShared_4143_ == 0 {
                    v___x_4145_ = v___x_4142_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
                    v___x_4145_ = v_reuseFailAlloc_4146_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4145_;
            }
            6 => {
                v_fst_4158_ = leanh::lean_ctor_get(v_a_4154_, 0);
                if leanh::lean_obj_tag(v_fst_4158_) == 0 {
                    v_snd_4159_ = leanh::lean_ctor_get(v_a_4154_, 1);
                    leanh::lean_inc(v_snd_4159_);
                    leanh::lean_dec(v_a_4154_);
                    v___x_4160_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4160_, 0, v_snd_4159_);
                    if v_isShared_4157_ == 0 {
                        leanh::lean_ctor_set(v___x_4156_, 0, v___x_4160_);
                        v___x_4162_ = v___x_4156_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4163_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4160_);
                        v___x_4162_ = v_reuseFailAlloc_4163_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4158_);
                    leanh::lean_dec(v_a_4154_);
                    v_val_4164_ = leanh::lean_ctor_get(v_fst_4158_, 0);
                    leanh::lean_inc(v_val_4164_);
                    leanh::lean_dec_ref_known(v_fst_4158_, 1);
                    if v_isShared_4157_ == 0 {
                        leanh::lean_ctor_set(v___x_4156_, 0, v_val_4164_);
                        v___x_4166_ = v___x_4156_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4167_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_val_4164_);
                        v___x_4166_ = v_reuseFailAlloc_4167_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_4162_;
            }
            8 => {
                return v___x_4166_;
            }
            9 => {
                if v_isShared_4172_ == 0 {
                    v___x_4174_ = v___x_4171_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4175_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
                    v___x_4174_ = v_reuseFailAlloc_4175_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4174_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(
    mut v_init_4177_: *mut leanh::LeanObject,
    mut v_ctx_4178_: *mut leanh::LeanObject,
    mut v_as_4179_: *mut leanh::LeanObject,
    mut v_sz_4180_: usize,
    mut v_i_4181_: usize,
    mut v_b_4182_: *mut leanh::LeanObject,
    mut v___y_4183_: *mut leanh::LeanObject,
    mut v___y_4184_: *mut leanh::LeanObject,
    mut v___y_4185_: *mut leanh::LeanObject,
    mut v___y_4186_: *mut leanh::LeanObject,
    mut v___y_4187_: *mut leanh::LeanObject,
    mut v___y_4188_: *mut leanh::LeanObject,
    mut v___y_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4194_: u8 = 0;
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v_a_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4205_: u8 = 0;
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: usize = 0;
    let mut v___x_4218_: usize = 0;
    let mut v_reuseFailAlloc_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v_a_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4225_: u8 = 0;
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v_unused_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4194_ = lean_usize_dec_lt(v_i_4181_, v_sz_4180_);
                if v___x_4194_ == 0 {
                    leanh::lean_dec_ref(v_ctx_4178_);
                    v___x_4195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4195_, 0, v_b_4182_);
                    return v___x_4195_;
                } else {
                    v_snd_4196_ = leanh::lean_ctor_get(v_b_4182_, 1);
                    v_isSharedCheck_4230_ = (!leanh::lean_is_exclusive(v_b_4182_)) as u8;
                    if v_isSharedCheck_4230_ == 0 {
                        v_unused_4231_ = leanh::lean_ctor_get(v_b_4182_, 0);
                        leanh::lean_dec(v_unused_4231_);
                        v___x_4198_ = v_b_4182_;
                        v_isShared_4199_ = v_isSharedCheck_4230_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4196_);
                        leanh::lean_dec(v_b_4182_);
                        v___x_4198_ = leanh::lean_box(0);
                        v_isShared_4199_ = v_isSharedCheck_4230_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4200_ = lean_array_uget_borrowed(v_as_4179_, v_i_4181_);
                leanh::lean_inc(v_snd_4196_);
                leanh::lean_inc_ref(v_ctx_4178_);
                v___x_4201_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_4177_, v_ctx_4178_, v_a_4200_, v_snd_4196_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
                if leanh::lean_obj_tag(v___x_4201_) == 0 {
                    v_a_4202_ = leanh::lean_ctor_get(v___x_4201_, 0);
                    v_isSharedCheck_4221_ = (!leanh::lean_is_exclusive(v___x_4201_)) as u8;
                    if v_isSharedCheck_4221_ == 0 {
                        v___x_4204_ = v___x_4201_;
                        v_isShared_4205_ = v_isSharedCheck_4221_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4202_);
                        leanh::lean_dec(v___x_4201_);
                        v___x_4204_ = leanh::lean_box(0);
                        v_isShared_4205_ = v_isSharedCheck_4221_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4198_);
                    leanh::lean_dec(v_snd_4196_);
                    leanh::lean_dec_ref(v_ctx_4178_);
                    v_a_4222_ = leanh::lean_ctor_get(v___x_4201_, 0);
                    v_isSharedCheck_4229_ = (!leanh::lean_is_exclusive(v___x_4201_)) as u8;
                    if v_isSharedCheck_4229_ == 0 {
                        v___x_4224_ = v___x_4201_;
                        v_isShared_4225_ = v_isSharedCheck_4229_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4222_);
                        leanh::lean_dec(v___x_4201_);
                        v___x_4224_ = leanh::lean_box(0);
                        v_isShared_4225_ = v_isSharedCheck_4229_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4202_) == 0 {
                    leanh::lean_dec_ref(v_ctx_4178_);
                    v___x_4206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4206_, 0, v_a_4202_);
                    if v_isShared_4199_ == 0 {
                        leanh::lean_ctor_set(v___x_4198_, 0, v___x_4206_);
                        v___x_4208_ = v___x_4198_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4212_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4206_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 1, v_snd_4196_);
                        v___x_4208_ = v_reuseFailAlloc_4212_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4204_);
                    leanh::lean_dec(v_snd_4196_);
                    v_a_4213_ = leanh::lean_ctor_get(v_a_4202_, 0);
                    leanh::lean_inc(v_a_4213_);
                    leanh::lean_dec_ref_known(v_a_4202_, 1);
                    v___x_4214_ = leanh::lean_box(0);
                    if v_isShared_4199_ == 0 {
                        leanh::lean_ctor_set(v___x_4198_, 1, v_a_4213_);
                        leanh::lean_ctor_set(v___x_4198_, 0, v___x_4214_);
                        v___x_4216_ = v___x_4198_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4220_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4214_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_a_4213_);
                        v___x_4216_ = v_reuseFailAlloc_4220_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4205_ == 0 {
                    leanh::lean_ctor_set(v___x_4204_, 0, v___x_4208_);
                    v___x_4210_ = v___x_4204_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
                    v___x_4210_ = v_reuseFailAlloc_4211_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4210_;
            }
            5 => {
                v___x_4217_ = 1usize;
                v___x_4218_ = lean_usize_add(v_i_4181_, v___x_4217_);
                v_i_4181_ = v___x_4218_;
                v_b_4182_ = v___x_4216_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4225_ == 0 {
                    v___x_4227_ = v___x_4224_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
                    v___x_4227_ = v_reuseFailAlloc_4228_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_init_4232_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_ctx_4233_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_as_4234_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_sz_4235_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_i_4236_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4237_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4238_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4239_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4240_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4241_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4242_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4243_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4244_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4245_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4246_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4247_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4248_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_4249_: usize = 0;
    let mut v_i_boxed_4250_: usize = 0;
    let mut v_res_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4249_ = leanh::lean_unbox_usize(v_sz_4235_);
    leanh::lean_dec(v_sz_4235_);
    v_i_boxed_4250_ = leanh::lean_unbox_usize(v_i_4236_);
    leanh::lean_dec(v_i_4236_);
    v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_4232_, v_ctx_4233_, v_as_4234_, v_sz_boxed_4249_, v_i_boxed_4250_, v_b_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
    leanh::lean_dec(v___y_4247_);
    leanh::lean_dec_ref(v___y_4246_);
    leanh::lean_dec(v___y_4245_);
    leanh::lean_dec_ref(v___y_4244_);
    leanh::lean_dec(v___y_4243_);
    leanh::lean_dec_ref(v___y_4242_);
    leanh::lean_dec(v___y_4241_);
    leanh::lean_dec_ref(v___y_4240_);
    leanh::lean_dec(v___y_4239_);
    leanh::lean_dec(v___y_4238_);
    leanh::lean_dec_ref(v_as_4234_);
    leanh::lean_dec_ref(v_init_4232_);
    return v_res_4251_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(
    mut v_init_4252_: *mut leanh::LeanObject,
    mut v_ctx_4253_: *mut leanh::LeanObject,
    mut v_n_4254_: *mut leanh::LeanObject,
    mut v_b_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
    mut v___y_4259_: *mut leanh::LeanObject,
    mut v___y_4260_: *mut leanh::LeanObject,
    mut v___y_4261_: *mut leanh::LeanObject,
    mut v___y_4262_: *mut leanh::LeanObject,
    mut v___y_4263_: *mut leanh::LeanObject,
    mut v___y_4264_: *mut leanh::LeanObject,
    mut v___y_4265_: *mut leanh::LeanObject,
    mut v___y_4266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4267_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_4252_, v_ctx_4253_, v_n_4254_, v_b_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
    leanh::lean_dec(v___y_4265_);
    leanh::lean_dec_ref(v___y_4264_);
    leanh::lean_dec(v___y_4263_);
    leanh::lean_dec_ref(v___y_4262_);
    leanh::lean_dec(v___y_4261_);
    leanh::lean_dec_ref(v___y_4260_);
    leanh::lean_dec(v___y_4259_);
    leanh::lean_dec_ref(v___y_4258_);
    leanh::lean_dec(v___y_4257_);
    leanh::lean_dec(v___y_4256_);
    leanh::lean_dec_ref(v_n_4254_);
    leanh::lean_dec_ref(v_init_4252_);
    return v_res_4267_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(
    mut v_ctx_4268_: *mut leanh::LeanObject,
    mut v_t_4269_: *mut leanh::LeanObject,
    mut v_init_4270_: *mut leanh::LeanObject,
    mut v___y_4271_: *mut leanh::LeanObject,
    mut v___y_4272_: *mut leanh::LeanObject,
    mut v___y_4273_: *mut leanh::LeanObject,
    mut v___y_4274_: *mut leanh::LeanObject,
    mut v___y_4275_: *mut leanh::LeanObject,
    mut v___y_4276_: *mut leanh::LeanObject,
    mut v___y_4277_: *mut leanh::LeanObject,
    mut v___y_4278_: *mut leanh::LeanObject,
    mut v___y_4279_: *mut leanh::LeanObject,
    mut v___y_4280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v_a_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4296_: usize = 0;
    let mut v___x_4297_: usize = 0;
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4302_: u8 = 0;
    let mut v_fst_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4312_: u8 = 0;
    let mut v_a_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_isSharedCheck_4321_: u8 = 0;
    let mut v_a_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4282_ = leanh::lean_ctor_get(v_t_4269_, 0);
                v_tail_4283_ = leanh::lean_ctor_get(v_t_4269_, 1);
                leanh::lean_inc_ref(v_ctx_4268_);
                leanh::lean_inc_ref(v_init_4270_);
                v___x_4284_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_4270_, v_ctx_4268_, v_root_4282_, v_init_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
                leanh::lean_dec_ref(v_init_4270_);
                if leanh::lean_obj_tag(v___x_4284_) == 0 {
                    v_a_4285_ = leanh::lean_ctor_get(v___x_4284_, 0);
                    v_isSharedCheck_4321_ = (!leanh::lean_is_exclusive(v___x_4284_)) as u8;
                    if v_isSharedCheck_4321_ == 0 {
                        v___x_4287_ = v___x_4284_;
                        v_isShared_4288_ = v_isSharedCheck_4321_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4285_);
                        leanh::lean_dec(v___x_4284_);
                        v___x_4287_ = leanh::lean_box(0);
                        v_isShared_4288_ = v_isSharedCheck_4321_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_ctx_4268_);
                    v_a_4322_ = leanh::lean_ctor_get(v___x_4284_, 0);
                    v_isSharedCheck_4329_ = (!leanh::lean_is_exclusive(v___x_4284_)) as u8;
                    if v_isSharedCheck_4329_ == 0 {
                        v___x_4324_ = v___x_4284_;
                        v_isShared_4325_ = v_isSharedCheck_4329_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4322_);
                        leanh::lean_dec(v___x_4284_);
                        v___x_4324_ = leanh::lean_box(0);
                        v_isShared_4325_ = v_isSharedCheck_4329_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4285_) == 0 {
                    leanh::lean_dec_ref(v_ctx_4268_);
                    v_a_4289_ = leanh::lean_ctor_get(v_a_4285_, 0);
                    leanh::lean_inc(v_a_4289_);
                    leanh::lean_dec_ref_known(v_a_4285_, 1);
                    if v_isShared_4288_ == 0 {
                        leanh::lean_ctor_set(v___x_4287_, 0, v_a_4289_);
                        v___x_4291_ = v___x_4287_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4292_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4289_);
                        v___x_4291_ = v_reuseFailAlloc_4292_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4287_);
                    v_a_4293_ = leanh::lean_ctor_get(v_a_4285_, 0);
                    leanh::lean_inc(v_a_4293_);
                    leanh::lean_dec_ref_known(v_a_4285_, 1);
                    v___x_4294_ = leanh::lean_box(0);
                    v___x_4295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4295_, 0, v___x_4294_);
                    leanh::lean_ctor_set(v___x_4295_, 1, v_a_4293_);
                    v_sz_4296_ = lean_array_size(v_tail_4283_);
                    v___x_4297_ = 0usize;
                    v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_4268_, v_tail_4283_, v_sz_4296_, v___x_4297_, v___x_4295_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
                    if leanh::lean_obj_tag(v___x_4298_) == 0 {
                        v_a_4299_ = leanh::lean_ctor_get(v___x_4298_, 0);
                        v_isSharedCheck_4312_ =
                            (!leanh::lean_is_exclusive(v___x_4298_)) as u8;
                        if v_isSharedCheck_4312_ == 0 {
                            v___x_4301_ = v___x_4298_;
                            v_isShared_4302_ = v_isSharedCheck_4312_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4299_);
                            leanh::lean_dec(v___x_4298_);
                            v___x_4301_ = leanh::lean_box(0);
                            v_isShared_4302_ = v_isSharedCheck_4312_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4313_ = leanh::lean_ctor_get(v___x_4298_, 0);
                        v_isSharedCheck_4320_ =
                            (!leanh::lean_is_exclusive(v___x_4298_)) as u8;
                        if v_isSharedCheck_4320_ == 0 {
                            v___x_4315_ = v___x_4298_;
                            v_isShared_4316_ = v_isSharedCheck_4320_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4313_);
                            leanh::lean_dec(v___x_4298_);
                            v___x_4315_ = leanh::lean_box(0);
                            v_isShared_4316_ = v_isSharedCheck_4320_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4291_;
            }
            3 => {
                v_fst_4303_ = leanh::lean_ctor_get(v_a_4299_, 0);
                if leanh::lean_obj_tag(v_fst_4303_) == 0 {
                    v_snd_4304_ = leanh::lean_ctor_get(v_a_4299_, 1);
                    leanh::lean_inc(v_snd_4304_);
                    leanh::lean_dec(v_a_4299_);
                    if v_isShared_4302_ == 0 {
                        leanh::lean_ctor_set(v___x_4301_, 0, v_snd_4304_);
                        v___x_4306_ = v___x_4301_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4307_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_snd_4304_);
                        v___x_4306_ = v_reuseFailAlloc_4307_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4303_);
                    leanh::lean_dec(v_a_4299_);
                    v_val_4308_ = leanh::lean_ctor_get(v_fst_4303_, 0);
                    leanh::lean_inc(v_val_4308_);
                    leanh::lean_dec_ref_known(v_fst_4303_, 1);
                    if v_isShared_4302_ == 0 {
                        leanh::lean_ctor_set(v___x_4301_, 0, v_val_4308_);
                        v___x_4310_ = v___x_4301_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_val_4308_);
                        v___x_4310_ = v_reuseFailAlloc_4311_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4306_;
            }
            5 => {
                return v___x_4310_;
            }
            6 => {
                if v_isShared_4316_ == 0 {
                    v___x_4318_ = v___x_4315_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4318_;
            }
            8 => {
                if v_isShared_4325_ == 0 {
                    v___x_4327_ = v___x_4324_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
                    v___x_4327_ = v_reuseFailAlloc_4328_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7___boxed(
    mut v_ctx_4330_: *mut leanh::LeanObject,
    mut v_t_4331_: *mut leanh::LeanObject,
    mut v_init_4332_: *mut leanh::LeanObject,
    mut v___y_4333_: *mut leanh::LeanObject,
    mut v___y_4334_: *mut leanh::LeanObject,
    mut v___y_4335_: *mut leanh::LeanObject,
    mut v___y_4336_: *mut leanh::LeanObject,
    mut v___y_4337_: *mut leanh::LeanObject,
    mut v___y_4338_: *mut leanh::LeanObject,
    mut v___y_4339_: *mut leanh::LeanObject,
    mut v___y_4340_: *mut leanh::LeanObject,
    mut v___y_4341_: *mut leanh::LeanObject,
    mut v___y_4342_: *mut leanh::LeanObject,
    mut v___y_4343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4344_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(
        v_ctx_4330_,
        v_t_4331_,
        v_init_4332_,
        v___y_4333_,
        v___y_4334_,
        v___y_4335_,
        v___y_4336_,
        v___y_4337_,
        v___y_4338_,
        v___y_4339_,
        v___y_4340_,
        v___y_4341_,
        v___y_4342_,
    );
    leanh::lean_dec(v___y_4342_);
    leanh::lean_dec_ref(v___y_4341_);
    leanh::lean_dec(v___y_4340_);
    leanh::lean_dec_ref(v___y_4339_);
    leanh::lean_dec(v___y_4338_);
    leanh::lean_dec_ref(v___y_4337_);
    leanh::lean_dec(v___y_4336_);
    leanh::lean_dec_ref(v___y_4335_);
    leanh::lean_dec(v___y_4334_);
    leanh::lean_dec(v___y_4333_);
    leanh::lean_dec_ref(v_t_4331_);
    return v_res_4344_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0;
    v___x_4349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5;
    v___x_4350_ = l_Lean_Name_append(v___x_4349_, v___x_4348_);
    return v___x_4350_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(
    mut v_as_4351_: *mut leanh::LeanObject,
    mut v_i_4352_: usize,
    mut v_stop_4353_: usize,
    mut v_b_4354_: *mut leanh::LeanObject,
    mut v___y_4355_: *mut leanh::LeanObject,
    mut v___y_4356_: *mut leanh::LeanObject,
    mut v___y_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
    mut v___y_4359_: *mut leanh::LeanObject,
    mut v___y_4360_: *mut leanh::LeanObject,
    mut v___y_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
    mut v___y_4363_: *mut leanh::LeanObject,
    mut v___y_4364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: usize = 0;
    let mut v___x_4369_: usize = 0;
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: u8 = 0;
    let mut v_a_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4397_: u8 = 0;
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4401_: u8 = 0;
    let mut v___y_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: u8 = 0;
    let mut v_a_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4421_: u8 = 0;
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4425_: u8 = 0;
    let mut v_a_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4429_: u8 = 0;
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4433_: u8 = 0;
    let mut v_options_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4435_: u8 = 0;
    let mut v_inheritedTraceOptions_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: u8 = 0;
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4445_: u8 = 0;
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4449_: u8 = 0;
    let mut v_a_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4371_ = lean_usize_dec_eq(v_i_4352_, v_stop_4353_);
                if v___x_4371_ == 0 {
                    v___x_4372_ = lean_array_uget_borrowed(v_as_4351_, v_i_4352_);
                    v___x_4373_ =
                        l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_4372_, v___y_4355_);
                    if leanh::lean_obj_tag(v___x_4373_) == 0 {
                        v_a_4374_ = leanh::lean_ctor_get(v___x_4373_, 0);
                        leanh::lean_inc(v_a_4374_);
                        leanh::lean_dec_ref_known(v___x_4373_, 1);
                        v___x_4375_ = (leanh::lean_unbox(v_a_4374_) as u8);
                        leanh::lean_dec(v_a_4374_);
                        if v___x_4375_ == 0 {
                            if leanh::lean_obj_tag(v___x_4372_) == 2 {
                                v_a_4376_ = leanh::lean_ctor_get(v___x_4372_, 0);
                                v_b_4377_ = leanh::lean_ctor_get(v___x_4372_, 1);
                                v_eq_4378_ = leanh::lean_ctor_get(v___x_4372_, 3);
                                v_options_4434_ = leanh::lean_ctor_get(v___y_4363_, 2);
                                v_hasTrace_4435_ = leanh::lean_ctor_get_uint8(
                                    v_options_4434_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                        as u32,
                                );
                                if v_hasTrace_4435_ == 0 {
                                    v___y_4403_ = v___y_4355_;
                                    v___y_4404_ = v___y_4356_;
                                    v___y_4405_ = v___y_4357_;
                                    v___y_4406_ = v___y_4358_;
                                    v___y_4407_ = v___y_4359_;
                                    v___y_4408_ = v___y_4360_;
                                    v___y_4409_ = v___y_4361_;
                                    v___y_4410_ = v___y_4362_;
                                    v___y_4411_ = v___y_4363_;
                                    v___y_4412_ = v___y_4364_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_inheritedTraceOptions_4436_ =
                                        leanh::lean_ctor_get(v___y_4363_, 13);
                                    v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0;
                                    v___x_4438_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
                                    v___x_4439_ =
                                        l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                            v_inheritedTraceOptions_4436_,
                                            v_options_4434_,
                                            v___x_4438_,
                                        );
                                    if v___x_4439_ == 0 {
                                        v___y_4403_ = v___y_4355_;
                                        v___y_4404_ = v___y_4356_;
                                        v___y_4405_ = v___y_4357_;
                                        v___y_4406_ = v___y_4358_;
                                        v___y_4407_ = v___y_4359_;
                                        v___y_4408_ = v___y_4360_;
                                        v___y_4409_ = v___y_4361_;
                                        v___y_4410_ = v___y_4362_;
                                        v___y_4411_ = v___y_4363_;
                                        v___y_4412_ = v___y_4364_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc_ref(v_eq_4378_);
                                        v___x_4440_ = l_Lean_MessageData_ofExpr(v_eq_4378_);
                                        v___x_4441_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_4437_, v___x_4440_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
                                        if leanh::lean_obj_tag(v___x_4441_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_4441_, 1);
                                            v___y_4403_ = v___y_4355_;
                                            v___y_4404_ = v___y_4356_;
                                            v___y_4405_ = v___y_4357_;
                                            v___y_4406_ = v___y_4358_;
                                            v___y_4407_ = v___y_4359_;
                                            v___y_4408_ = v___y_4360_;
                                            v___y_4409_ = v___y_4361_;
                                            v___y_4410_ = v___y_4362_;
                                            v___y_4411_ = v___y_4363_;
                                            v___y_4412_ = v___y_4364_;
                                            state = 5;
                                            continue;
                                        } else {
                                            leanh::lean_dec_ref(v_b_4354_);
                                            v_a_4442_ = leanh::lean_ctor_get(v___x_4441_, 0);
                                            v_isSharedCheck_4449_ =
                                                (!leanh::lean_is_exclusive(v___x_4441_))
                                                    as u8;
                                            if v_isSharedCheck_4449_ == 0 {
                                                v___x_4444_ = v___x_4441_;
                                                v_isShared_4445_ = v_isSharedCheck_4449_;
                                                state = 10;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4442_);
                                                leanh::lean_dec(v___x_4441_);
                                                v___x_4444_ = leanh::lean_box(0);
                                                v_isShared_4445_ = v_isSharedCheck_4449_;
                                                state = 10;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                v_a_4367_ = v_b_4354_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4367_ = v_b_4354_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_4354_);
                        v_a_4450_ = leanh::lean_ctor_get(v___x_4373_, 0);
                        v_isSharedCheck_4457_ =
                            (!leanh::lean_is_exclusive(v___x_4373_)) as u8;
                        if v_isSharedCheck_4457_ == 0 {
                            v___x_4452_ = v___x_4373_;
                            v_isShared_4453_ = v_isSharedCheck_4457_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4450_);
                            leanh::lean_dec(v___x_4373_);
                            v___x_4452_ = leanh::lean_box(0);
                            v_isShared_4453_ = v_isSharedCheck_4457_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    v___x_4458_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4458_, 0, v_b_4354_);
                    return v___x_4458_;
                }
            }
            1 => {
                v___x_4368_ = 1usize;
                v___x_4369_ = lean_usize_add(v_i_4352_, v___x_4368_);
                v_i_4352_ = v___x_4369_;
                v_b_4354_ = v_a_4367_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4391_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_4385_);
                leanh::lean_inc_ref(v___y_4381_);
                leanh::lean_inc(v___y_4383_);
                leanh::lean_inc_ref(v___y_4380_);
                leanh::lean_inc(v___y_4388_);
                leanh::lean_inc_ref(v___y_4386_);
                leanh::lean_inc(v___y_4389_);
                leanh::lean_inc_ref(v___y_4384_);
                leanh::lean_inc(v___y_4387_);
                leanh::lean_inc(v___y_4382_);
                leanh::lean_inc_ref(v_eq_4378_);
                v___x_4392_ = lean_grind_internalize(
                    v_eq_4378_,
                    v___y_4390_,
                    v___x_4391_,
                    v___y_4382_,
                    v___y_4387_,
                    v___y_4384_,
                    v___y_4389_,
                    v___y_4386_,
                    v___y_4388_,
                    v___y_4380_,
                    v___y_4383_,
                    v___y_4381_,
                    v___y_4385_,
                );
                if leanh::lean_obj_tag(v___x_4392_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4392_, 1);
                    leanh::lean_inc_ref(v___x_4372_);
                    v___x_4393_ = lean_array_push(v_b_4354_, v___x_4372_);
                    v_a_4367_ = v___x_4393_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_4354_);
                    v_a_4394_ = leanh::lean_ctor_get(v___x_4392_, 0);
                    v_isSharedCheck_4401_ = (!leanh::lean_is_exclusive(v___x_4392_)) as u8;
                    if v_isSharedCheck_4401_ == 0 {
                        v___x_4396_ = v___x_4392_;
                        v_isShared_4397_ = v_isSharedCheck_4401_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4394_);
                        leanh::lean_dec(v___x_4392_);
                        v___x_4396_ = leanh::lean_box(0);
                        v_isShared_4397_ = v_isSharedCheck_4401_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4397_ == 0 {
                    v___x_4399_ = v___x_4396_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4400_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
                    v___x_4399_ = v_reuseFailAlloc_4400_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4399_;
            }
            5 => {
                v___x_4413_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_4376_, v___y_4403_);
                if leanh::lean_obj_tag(v___x_4413_) == 0 {
                    v_a_4414_ = leanh::lean_ctor_get(v___x_4413_, 0);
                    leanh::lean_inc(v_a_4414_);
                    leanh::lean_dec_ref_known(v___x_4413_, 1);
                    v___x_4415_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4377_, v___y_4403_);
                    if leanh::lean_obj_tag(v___x_4415_) == 0 {
                        v_a_4416_ = leanh::lean_ctor_get(v___x_4415_, 0);
                        leanh::lean_inc(v_a_4416_);
                        leanh::lean_dec_ref_known(v___x_4415_, 1);
                        v___x_4417_ = lean_nat_dec_le(v_a_4414_, v_a_4416_);
                        if v___x_4417_ == 0 {
                            leanh::lean_dec(v_a_4416_);
                            v___y_4380_ = v___y_4409_;
                            v___y_4381_ = v___y_4411_;
                            v___y_4382_ = v___y_4403_;
                            v___y_4383_ = v___y_4410_;
                            v___y_4384_ = v___y_4405_;
                            v___y_4385_ = v___y_4412_;
                            v___y_4386_ = v___y_4407_;
                            v___y_4387_ = v___y_4404_;
                            v___y_4388_ = v___y_4408_;
                            v___y_4389_ = v___y_4406_;
                            v___y_4390_ = v_a_4414_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_4414_);
                            v___y_4380_ = v___y_4409_;
                            v___y_4381_ = v___y_4411_;
                            v___y_4382_ = v___y_4403_;
                            v___y_4383_ = v___y_4410_;
                            v___y_4384_ = v___y_4405_;
                            v___y_4385_ = v___y_4412_;
                            v___y_4386_ = v___y_4407_;
                            v___y_4387_ = v___y_4404_;
                            v___y_4388_ = v___y_4408_;
                            v___y_4389_ = v___y_4406_;
                            v___y_4390_ = v_a_4416_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4414_);
                        leanh::lean_dec_ref(v_b_4354_);
                        v_a_4418_ = leanh::lean_ctor_get(v___x_4415_, 0);
                        v_isSharedCheck_4425_ =
                            (!leanh::lean_is_exclusive(v___x_4415_)) as u8;
                        if v_isSharedCheck_4425_ == 0 {
                            v___x_4420_ = v___x_4415_;
                            v_isShared_4421_ = v_isSharedCheck_4425_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4418_);
                            leanh::lean_dec(v___x_4415_);
                            v___x_4420_ = leanh::lean_box(0);
                            v_isShared_4421_ = v_isSharedCheck_4425_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_4354_);
                    v_a_4426_ = leanh::lean_ctor_get(v___x_4413_, 0);
                    v_isSharedCheck_4433_ = (!leanh::lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4433_ == 0 {
                        v___x_4428_ = v___x_4413_;
                        v_isShared_4429_ = v_isSharedCheck_4433_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4426_);
                        leanh::lean_dec(v___x_4413_);
                        v___x_4428_ = leanh::lean_box(0);
                        v_isShared_4429_ = v_isSharedCheck_4433_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4421_ == 0 {
                    v___x_4423_ = v___x_4420_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4424_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
                    v___x_4423_ = v_reuseFailAlloc_4424_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4423_;
            }
            8 => {
                if v_isShared_4429_ == 0 {
                    v___x_4431_ = v___x_4428_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
                    v___x_4431_ = v_reuseFailAlloc_4432_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4431_;
            }
            10 => {
                if v_isShared_4445_ == 0 {
                    v___x_4447_ = v___x_4444_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4448_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
                    v___x_4447_ = v_reuseFailAlloc_4448_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4447_;
            }
            12 => {
                if v_isShared_4453_ == 0 {
                    v___x_4455_ = v___x_4452_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
                    v___x_4455_ = v_reuseFailAlloc_4456_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___boxed(
    mut v_as_4459_: *mut leanh::LeanObject,
    mut v_i_4460_: *mut leanh::LeanObject,
    mut v_stop_4461_: *mut leanh::LeanObject,
    mut v_b_4462_: *mut leanh::LeanObject,
    mut v___y_4463_: *mut leanh::LeanObject,
    mut v___y_4464_: *mut leanh::LeanObject,
    mut v___y_4465_: *mut leanh::LeanObject,
    mut v___y_4466_: *mut leanh::LeanObject,
    mut v___y_4467_: *mut leanh::LeanObject,
    mut v___y_4468_: *mut leanh::LeanObject,
    mut v___y_4469_: *mut leanh::LeanObject,
    mut v___y_4470_: *mut leanh::LeanObject,
    mut v___y_4471_: *mut leanh::LeanObject,
    mut v___y_4472_: *mut leanh::LeanObject,
    mut v___y_4473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4474_: usize = 0;
    let mut v_stop_boxed_4475_: usize = 0;
    let mut v_res_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4474_ = leanh::lean_unbox_usize(v_i_4460_);
    leanh::lean_dec(v_i_4460_);
    v_stop_boxed_4475_ = leanh::lean_unbox_usize(v_stop_4461_);
    leanh::lean_dec(v_stop_4461_);
    v_res_4476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_4459_, v_i_boxed_4474_, v_stop_boxed_4475_, v_b_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
    leanh::lean_dec(v___y_4472_);
    leanh::lean_dec_ref(v___y_4471_);
    leanh::lean_dec(v___y_4470_);
    leanh::lean_dec_ref(v___y_4469_);
    leanh::lean_dec(v___y_4468_);
    leanh::lean_dec_ref(v___y_4467_);
    leanh::lean_dec(v___y_4466_);
    leanh::lean_dec_ref(v___y_4465_);
    leanh::lean_dec(v___y_4464_);
    leanh::lean_dec(v___y_4463_);
    leanh::lean_dec_ref(v_as_4459_);
    return v_res_4476_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(
    mut v_as_4479_: *mut leanh::LeanObject,
    mut v_start_4480_: *mut leanh::LeanObject,
    mut v_stop_4481_: *mut leanh::LeanObject,
    mut v___y_4482_: *mut leanh::LeanObject,
    mut v___y_4483_: *mut leanh::LeanObject,
    mut v___y_4484_: *mut leanh::LeanObject,
    mut v___y_4485_: *mut leanh::LeanObject,
    mut v___y_4486_: *mut leanh::LeanObject,
    mut v___y_4487_: *mut leanh::LeanObject,
    mut v___y_4488_: *mut leanh::LeanObject,
    mut v___y_4489_: *mut leanh::LeanObject,
    mut v___y_4490_: *mut leanh::LeanObject,
    mut v___y_4491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    v___x_4493_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0;
    v___x_4494_ = lean_nat_dec_lt(v_start_4480_, v_stop_4481_);
    if v___x_4494_ == 0 {
        let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4495_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4495_, 0, v___x_4493_);
        return v___x_4495_;
    } else {
        let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4497_: u8 = 0;
        v___x_4496_ = lean_array_get_size(v_as_4479_);
        v___x_4497_ = lean_nat_dec_le(v_stop_4481_, v___x_4496_);
        if v___x_4497_ == 0 {
            let mut v___x_4498_: u8 = 0;
            v___x_4498_ = lean_nat_dec_lt(v_start_4480_, v___x_4496_);
            if v___x_4498_ == 0 {
                let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4499_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4499_, 0, v___x_4493_);
                return v___x_4499_;
            } else {
                let mut v___x_4500_: usize = 0;
                let mut v___x_4501_: usize = 0;
                let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4500_ = lean_usize_of_nat(v_start_4480_);
                v___x_4501_ = lean_usize_of_nat(v___x_4496_);
                v___x_4502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_4479_, v___x_4500_, v___x_4501_, v___x_4493_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
                return v___x_4502_;
            }
        } else {
            let mut v___x_4503_: usize = 0;
            let mut v___x_4504_: usize = 0;
            let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4503_ = lean_usize_of_nat(v_start_4480_);
            v___x_4504_ = lean_usize_of_nat(v_stop_4481_);
            v___x_4505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_4479_, v___x_4503_, v___x_4504_, v___x_4493_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
            return v___x_4505_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(
    mut v_as_4506_: *mut leanh::LeanObject,
    mut v_start_4507_: *mut leanh::LeanObject,
    mut v_stop_4508_: *mut leanh::LeanObject,
    mut v___y_4509_: *mut leanh::LeanObject,
    mut v___y_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
    mut v___y_4512_: *mut leanh::LeanObject,
    mut v___y_4513_: *mut leanh::LeanObject,
    mut v___y_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
    mut v___y_4516_: *mut leanh::LeanObject,
    mut v___y_4517_: *mut leanh::LeanObject,
    mut v___y_4518_: *mut leanh::LeanObject,
    mut v___y_4519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4520_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(
        v_as_4506_,
        v_start_4507_,
        v_stop_4508_,
        v___y_4509_,
        v___y_4510_,
        v___y_4511_,
        v___y_4512_,
        v___y_4513_,
        v___y_4514_,
        v___y_4515_,
        v___y_4516_,
        v___y_4517_,
        v___y_4518_,
    );
    leanh::lean_dec(v___y_4518_);
    leanh::lean_dec_ref(v___y_4517_);
    leanh::lean_dec(v___y_4516_);
    leanh::lean_dec_ref(v___y_4515_);
    leanh::lean_dec(v___y_4514_);
    leanh::lean_dec_ref(v___y_4513_);
    leanh::lean_dec(v___y_4512_);
    leanh::lean_dec_ref(v___y_4511_);
    leanh::lean_dec(v___y_4510_);
    leanh::lean_dec(v___y_4509_);
    leanh::lean_dec(v_stop_4508_);
    leanh::lean_dec(v_start_4507_);
    leanh::lean_dec_ref(v_as_4506_);
    return v_res_4520_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = leanh::lean_box(0);
    v___x_4522_ = leanh::lean_unsigned_to_nat(16);
    v___x_4523_ = lean_mk_array(v___x_4522_, v___x_4521_);
    return v___x_4523_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4524_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__0_once),
        _init_l_Lean_Meta_Grind_mbtc___closed__0,
    );
    v___x_4525_ = leanh::lean_unsigned_to_nat(0);
    v___x_4526_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4526_, 0, v___x_4525_);
    leanh::lean_ctor_set(v___x_4526_, 1, v___x_4524_);
    return v___x_4526_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4527_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__1_once),
        _init_l_Lean_Meta_Grind_mbtc___closed__1,
    );
    v___x_4528_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4528_, 0, v___x_4527_);
    leanh::lean_ctor_set(v___x_4528_, 1, v___x_4527_);
    return v___x_4528_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4530_ = l_Lean_Meta_Grind_mbtc___closed__3;
    v___x_4531_ = l_Lean_stringToMessageData(v___x_4530_);
    return v___x_4531_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4533_ = l_Lean_Meta_Grind_mbtc___closed__5;
    v___x_4534_ = l_Lean_stringToMessageData(v___x_4533_);
    return v___x_4534_;
}
pub unsafe fn l_Lean_Meta_Grind_mbtc(
    mut v_ctx_4535_: *mut leanh::LeanObject,
    mut v_a_4536_: *mut leanh::LeanObject,
    mut v_a_4537_: *mut leanh::LeanObject,
    mut v_a_4538_: *mut leanh::LeanObject,
    mut v_a_4539_: *mut leanh::LeanObject,
    mut v_a_4540_: *mut leanh::LeanObject,
    mut v_a_4541_: *mut leanh::LeanObject,
    mut v_a_4542_: *mut leanh::LeanObject,
    mut v_a_4543_: *mut leanh::LeanObject,
    mut v_a_4544_: *mut leanh::LeanObject,
    mut v_a_4545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4551_: u8 = 0;
    let mut v_mbtc_4552_: u8 = 0;
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4561_: u8 = 0;
    let mut v___x_4562_: u8 = 0;
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4572_: u8 = 0;
    let mut v_snd_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4578_: u8 = 0;
    let mut v___x_4579_: u8 = 0;
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4590_: u8 = 0;
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: u8 = 0;
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4594_: usize = 0;
    let mut v___x_4595_: usize = 0;
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4599_: u8 = 0;
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4604_: u8 = 0;
    let mut v_unused_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4609_: u8 = 0;
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_a_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v___y_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: u8 = 0;
    let mut v___y_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: u8 = 0;
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: u8 = 0;
    let mut v_toGoalState_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v_split_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_splits_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: u8 = 0;
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut v___x_4657_: u8 = 0;
    let mut v___x_4658_: usize = 0;
    let mut v___x_4659_: usize = 0;
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: usize = 0;
    let mut v___x_4662_: usize = 0;
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_splits_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4689_: u8 = 0;
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4694_: u8 = 0;
    let mut v_unused_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4699_: u8 = 0;
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4703_: u8 = 0;
    let mut v_reuseFailAlloc_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4706_: u8 = 0;
    let mut v_a_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4710_: u8 = 0;
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4714_: u8 = 0;
    let mut v_a_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4718_: u8 = 0;
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4722_: u8 = 0;
    let mut v_isSharedCheck_4723_: u8 = 0;
    let mut v_unused_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4728_: u8 = 0;
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4732_: u8 = 0;
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v_a_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4741_: u8 = 0;
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4745_: u8 = 0;
    let mut v___x_4746_: u8 = 0;
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4751_: u8 = 0;
    let mut v_isSharedCheck_4752_: u8 = 0;
    let mut v_a_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4756_: u8 = 0;
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4547_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4538_);
                if leanh::lean_obj_tag(v___x_4547_) == 0 {
                    v_a_4548_ = leanh::lean_ctor_get(v___x_4547_, 0);
                    v_isSharedCheck_4752_ = (!leanh::lean_is_exclusive(v___x_4547_)) as u8;
                    if v_isSharedCheck_4752_ == 0 {
                        v___x_4550_ = v___x_4547_;
                        v_isShared_4551_ = v_isSharedCheck_4752_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4548_);
                        leanh::lean_dec(v___x_4547_);
                        v___x_4550_ = leanh::lean_box(0);
                        v_isShared_4551_ = v_isSharedCheck_4752_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_ctx_4535_);
                    v_a_4753_ = leanh::lean_ctor_get(v___x_4547_, 0);
                    v_isSharedCheck_4760_ = (!leanh::lean_is_exclusive(v___x_4547_)) as u8;
                    if v_isSharedCheck_4760_ == 0 {
                        v___x_4755_ = v___x_4547_;
                        v_isShared_4756_ = v_isSharedCheck_4760_;
                        state = 37;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4753_);
                        leanh::lean_dec(v___x_4547_);
                        v___x_4755_ = leanh::lean_box(0);
                        v_isShared_4756_ = v_isSharedCheck_4760_;
                        state = 37;
                        continue;
                    }
                }
            }
            1 => {
                v_mbtc_4552_ = leanh::lean_ctor_get_uint8(
                    v_a_4548_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 18) as u32,
                );
                leanh::lean_dec(v_a_4548_);
                if v_mbtc_4552_ == 0 {
                    leanh::lean_dec_ref(v_ctx_4535_);
                    v___x_4553_ = leanh::lean_box((v_mbtc_4552_) as usize);
                    if v_isShared_4551_ == 0 {
                        leanh::lean_ctor_set(v___x_4550_, 0, v___x_4553_);
                        v___x_4555_ = v___x_4550_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4556_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
                        v___x_4555_ = v_reuseFailAlloc_4556_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4550_);
                    v___x_4557_ =
                        l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_4536_, v_a_4538_);
                    if leanh::lean_obj_tag(v___x_4557_) == 0 {
                        v_a_4558_ = leanh::lean_ctor_get(v___x_4557_, 0);
                        v_isSharedCheck_4751_ =
                            (!leanh::lean_is_exclusive(v___x_4557_)) as u8;
                        if v_isSharedCheck_4751_ == 0 {
                            v___x_4560_ = v___x_4557_;
                            v_isShared_4561_ = v_isSharedCheck_4751_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4558_);
                            leanh::lean_dec(v___x_4557_);
                            v___x_4560_ = leanh::lean_box(0);
                            v_isShared_4561_ = v_isSharedCheck_4751_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_ctx_4535_);
                        return v___x_4557_;
                    }
                }
            }
            2 => {
                return v___x_4555_;
            }
            3 => {
                v___x_4562_ = (leanh::lean_unbox(v_a_4558_) as u8);
                if v___x_4562_ == 0 {
                    leanh::lean_del_object(v___x_4560_);
                    v___x_4563_ = lean_st_ref_get(v_a_4536_);
                    v_toGoalState_4564_ = leanh::lean_ctor_get(v___x_4563_, 0);
                    leanh::lean_inc_ref(v_toGoalState_4564_);
                    leanh::lean_dec(v___x_4563_);
                    v_exprs_4565_ = leanh::lean_ctor_get(v_toGoalState_4564_, 2);
                    leanh::lean_inc_ref(v_exprs_4565_);
                    leanh::lean_dec_ref(v_toGoalState_4564_);
                    v___x_4566_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4567_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__2_once),
                        _init_l_Lean_Meta_Grind_mbtc___closed__2,
                    );
                    v___x_4568_ =
                        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(
                            v_ctx_4535_,
                            v_exprs_4565_,
                            v___x_4567_,
                            v_a_4536_,
                            v_a_4537_,
                            v_a_4538_,
                            v_a_4539_,
                            v_a_4540_,
                            v_a_4541_,
                            v_a_4542_,
                            v_a_4543_,
                            v_a_4544_,
                            v_a_4545_,
                        );
                    leanh::lean_dec_ref(v_exprs_4565_);
                    if leanh::lean_obj_tag(v___x_4568_) == 0 {
                        v_a_4569_ = leanh::lean_ctor_get(v___x_4568_, 0);
                        v_isSharedCheck_4737_ =
                            (!leanh::lean_is_exclusive(v___x_4568_)) as u8;
                        if v_isSharedCheck_4737_ == 0 {
                            v___x_4571_ = v___x_4568_;
                            v_isShared_4572_ = v_isSharedCheck_4737_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4569_);
                            leanh::lean_dec(v___x_4568_);
                            v___x_4571_ = leanh::lean_box(0);
                            v_isShared_4572_ = v_isSharedCheck_4737_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4558_);
                        v_a_4738_ = leanh::lean_ctor_get(v___x_4568_, 0);
                        v_isSharedCheck_4745_ =
                            (!leanh::lean_is_exclusive(v___x_4568_)) as u8;
                        if v_isSharedCheck_4745_ == 0 {
                            v___x_4740_ = v___x_4568_;
                            v_isShared_4741_ = v_isSharedCheck_4745_;
                            state = 34;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4738_);
                            leanh::lean_dec(v___x_4568_);
                            v___x_4740_ = leanh::lean_box(0);
                            v_isShared_4741_ = v_isSharedCheck_4745_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4558_);
                    leanh::lean_dec_ref(v_ctx_4535_);
                    v___x_4746_ = 0;
                    v___x_4747_ = leanh::lean_box((v___x_4746_) as usize);
                    if v_isShared_4561_ == 0 {
                        leanh::lean_ctor_set(v___x_4560_, 0, v___x_4747_);
                        v___x_4749_ = v___x_4560_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_4750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
                        v___x_4749_ = v_reuseFailAlloc_4750_;
                        state = 36;
                        continue;
                    }
                }
            }
            4 => {
                v_snd_4573_ = leanh::lean_ctor_get(v_a_4569_, 1);
                leanh::lean_inc(v_snd_4573_);
                leanh::lean_dec(v_a_4569_);
                v_size_4574_ = leanh::lean_ctor_get(v_snd_4573_, 0);
                v_buckets_4575_ = leanh::lean_ctor_get(v_snd_4573_, 1);
                v_isSharedCheck_4736_ = (!leanh::lean_is_exclusive(v_snd_4573_)) as u8;
                if v_isSharedCheck_4736_ == 0 {
                    v___x_4577_ = v_snd_4573_;
                    v_isShared_4578_ = v_isSharedCheck_4736_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_4575_);
                    leanh::lean_inc(v_size_4574_);
                    leanh::lean_dec(v_snd_4573_);
                    v___x_4577_ = leanh::lean_box(0);
                    v_isShared_4578_ = v_isSharedCheck_4736_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4579_ = lean_nat_dec_eq(v_size_4574_, v___x_4566_);
                if v___x_4579_ == 0 {
                    leanh::lean_del_object(v___x_4571_);
                    leanh::lean_dec(v_a_4558_);
                    v___x_4580_ = lean_st_ref_get(v_a_4536_);
                    v___x_4581_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4538_);
                    if leanh::lean_obj_tag(v___x_4581_) == 0 {
                        v_a_4582_ = leanh::lean_ctor_get(v___x_4581_, 0);
                        leanh::lean_inc(v_a_4582_);
                        leanh::lean_dec_ref_known(v___x_4581_, 1);
                        v_toGoalState_4646_ = leanh::lean_ctor_get(v___x_4580_, 0);
                        v_isSharedCheck_4723_ =
                            (!leanh::lean_is_exclusive(v___x_4580_)) as u8;
                        if v_isSharedCheck_4723_ == 0 {
                            v_unused_4724_ = leanh::lean_ctor_get(v___x_4580_, 1);
                            leanh::lean_dec(v_unused_4724_);
                            v___x_4648_ = v___x_4580_;
                            v_isShared_4649_ = v_isSharedCheck_4723_;
                            state = 18;
                            continue;
                        } else {
                            leanh::lean_inc(v_toGoalState_4646_);
                            leanh::lean_dec(v___x_4580_);
                            v___x_4648_ = leanh::lean_box(0);
                            v_isShared_4649_ = v_isSharedCheck_4723_;
                            state = 18;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4580_);
                        leanh::lean_del_object(v___x_4577_);
                        leanh::lean_dec_ref(v_buckets_4575_);
                        leanh::lean_dec(v_size_4574_);
                        v_a_4725_ = leanh::lean_ctor_get(v___x_4581_, 0);
                        v_isSharedCheck_4732_ =
                            (!leanh::lean_is_exclusive(v___x_4581_)) as u8;
                        if v_isSharedCheck_4732_ == 0 {
                            v___x_4727_ = v___x_4581_;
                            v_isShared_4728_ = v_isSharedCheck_4732_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4725_);
                            leanh::lean_dec(v___x_4581_);
                            v___x_4727_ = leanh::lean_box(0);
                            v_isShared_4728_ = v_isSharedCheck_4732_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4577_);
                    leanh::lean_dec_ref(v_buckets_4575_);
                    leanh::lean_dec(v_size_4574_);
                    if v_isShared_4572_ == 0 {
                        leanh::lean_ctor_set(v___x_4571_, 0, v_a_4558_);
                        v___x_4734_ = v___x_4571_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_4735_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4558_);
                        v___x_4734_ = v_reuseFailAlloc_4735_;
                        state = 33;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4585_ = lean_array_get_size(v___y_4584_);
                v___x_4586_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(
                    v___y_4584_,
                    v___x_4566_,
                    v___x_4585_,
                    v_a_4536_,
                    v_a_4537_,
                    v_a_4538_,
                    v_a_4539_,
                    v_a_4540_,
                    v_a_4541_,
                    v_a_4542_,
                    v_a_4543_,
                    v_a_4544_,
                    v_a_4545_,
                );
                leanh::lean_dec_ref(v___y_4584_);
                if leanh::lean_obj_tag(v___x_4586_) == 0 {
                    v_a_4587_ = leanh::lean_ctor_get(v___x_4586_, 0);
                    v_isSharedCheck_4618_ = (!leanh::lean_is_exclusive(v___x_4586_)) as u8;
                    if v_isSharedCheck_4618_ == 0 {
                        v___x_4589_ = v___x_4586_;
                        v_isShared_4590_ = v_isSharedCheck_4618_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4587_);
                        leanh::lean_dec(v___x_4586_);
                        v___x_4589_ = leanh::lean_box(0);
                        v_isShared_4590_ = v_isSharedCheck_4618_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_4619_ = leanh::lean_ctor_get(v___x_4586_, 0);
                    v_isSharedCheck_4626_ = (!leanh::lean_is_exclusive(v___x_4586_)) as u8;
                    if v_isSharedCheck_4626_ == 0 {
                        v___x_4621_ = v___x_4586_;
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4619_);
                        leanh::lean_dec(v___x_4586_);
                        v___x_4621_ = leanh::lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4591_ = lean_array_get_size(v_a_4587_);
                v___x_4592_ = lean_nat_dec_eq(v___x_4591_, v___x_4566_);
                if v___x_4592_ == 0 {
                    leanh::lean_del_object(v___x_4589_);
                    v___x_4593_ = leanh::lean_box(0);
                    v_sz_4594_ = lean_array_size(v_a_4587_);
                    v___x_4595_ = 0usize;
                    v___x_4596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_4587_, v_sz_4594_, v___x_4595_, v___x_4593_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
                    leanh::lean_dec(v_a_4587_);
                    if leanh::lean_obj_tag(v___x_4596_) == 0 {
                        v_isSharedCheck_4604_ =
                            (!leanh::lean_is_exclusive(v___x_4596_)) as u8;
                        if v_isSharedCheck_4604_ == 0 {
                            v_unused_4605_ = leanh::lean_ctor_get(v___x_4596_, 0);
                            leanh::lean_dec(v_unused_4605_);
                            v___x_4598_ = v___x_4596_;
                            v_isShared_4599_ = v_isSharedCheck_4604_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4596_);
                            v___x_4598_ = leanh::lean_box(0);
                            v_isShared_4599_ = v_isSharedCheck_4604_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_4606_ = leanh::lean_ctor_get(v___x_4596_, 0);
                        v_isSharedCheck_4613_ =
                            (!leanh::lean_is_exclusive(v___x_4596_)) as u8;
                        if v_isSharedCheck_4613_ == 0 {
                            v___x_4608_ = v___x_4596_;
                            v_isShared_4609_ = v_isSharedCheck_4613_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4606_);
                            leanh::lean_dec(v___x_4596_);
                            v___x_4608_ = leanh::lean_box(0);
                            v_isShared_4609_ = v_isSharedCheck_4613_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4587_);
                    v___x_4614_ = leanh::lean_box((v___x_4579_) as usize);
                    if v_isShared_4590_ == 0 {
                        leanh::lean_ctor_set(v___x_4589_, 0, v___x_4614_);
                        v___x_4616_ = v___x_4589_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4617_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4614_);
                        v___x_4616_ = v_reuseFailAlloc_4617_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                v___x_4600_ = leanh::lean_box((v_mbtc_4552_) as usize);
                if v_isShared_4599_ == 0 {
                    leanh::lean_ctor_set(v___x_4598_, 0, v___x_4600_);
                    v___x_4602_ = v___x_4598_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4603_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4600_);
                    v___x_4602_ = v_reuseFailAlloc_4603_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4602_;
            }
            10 => {
                if v_isShared_4609_ == 0 {
                    v___x_4611_ = v___x_4608_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4612_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
                    v___x_4611_ = v_reuseFailAlloc_4612_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4611_;
            }
            12 => {
                return v___x_4616_;
            }
            13 => {
                if v_isShared_4622_ == 0 {
                    v___x_4624_ = v___x_4621_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4624_;
            }
            15 => {
                v___x_4632_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v___y_4629_, v___y_4630_, v___y_4628_, v___y_4631_);
                leanh::lean_dec(v___y_4631_);
                leanh::lean_dec(v___y_4629_);
                v___y_4584_ = v___x_4632_;
                state = 6;
                continue;
            }
            16 => {
                v___x_4638_ = lean_nat_dec_le(v___y_4637_, v___y_4634_);
                if v___x_4638_ == 0 {
                    leanh::lean_dec(v___y_4634_);
                    leanh::lean_inc(v___y_4637_);
                    v___y_4628_ = v___y_4637_;
                    v___y_4629_ = v___y_4635_;
                    v___y_4630_ = v___y_4636_;
                    v___y_4631_ = v___y_4637_;
                    state = 15;
                    continue;
                } else {
                    v___y_4628_ = v___y_4637_;
                    v___y_4629_ = v___y_4635_;
                    v___y_4630_ = v___y_4636_;
                    v___y_4631_ = v___y_4634_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                v___x_4641_ = lean_array_get_size(v___y_4640_);
                v___x_4642_ = lean_nat_dec_eq(v___x_4641_, v___x_4566_);
                if v___x_4642_ == 0 {
                    v___x_4643_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4644_ = lean_nat_sub(v___x_4641_, v___x_4643_);
                    v___x_4645_ = lean_nat_dec_le(v___x_4566_, v___x_4644_);
                    if v___x_4645_ == 0 {
                        leanh::lean_inc(v___x_4644_);
                        v___y_4634_ = v___x_4644_;
                        v___y_4635_ = v___x_4641_;
                        v___y_4636_ = v___y_4640_;
                        v___y_4637_ = v___x_4644_;
                        state = 16;
                        continue;
                    } else {
                        v___y_4634_ = v___x_4644_;
                        v___y_4635_ = v___x_4641_;
                        v___y_4636_ = v___y_4640_;
                        v___y_4637_ = v___x_4566_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___y_4584_ = v___y_4640_;
                    state = 6;
                    continue;
                }
            }
            18 => {
                v_split_4650_ = leanh::lean_ctor_get(v_toGoalState_4646_, 14);
                leanh::lean_inc_ref(v_split_4650_);
                leanh::lean_dec_ref(v_toGoalState_4646_);
                v_splits_4651_ = leanh::lean_ctor_get(v_a_4582_, 0);
                leanh::lean_inc(v_splits_4651_);
                leanh::lean_dec(v_a_4582_);
                v_num_4652_ = leanh::lean_ctor_get(v_split_4650_, 0);
                leanh::lean_inc(v_num_4652_);
                leanh::lean_dec_ref(v_split_4650_);
                v___x_4653_ = lean_nat_dec_lt(v_splits_4651_, v_num_4652_);
                leanh::lean_dec(v_num_4652_);
                leanh::lean_dec(v_splits_4651_);
                if v___x_4653_ == 0 {
                    leanh::lean_del_object(v___x_4648_);
                    leanh::lean_del_object(v___x_4577_);
                    v___x_4654_ = lean_mk_empty_array_with_capacity(v_size_4574_);
                    leanh::lean_dec(v_size_4574_);
                    v___x_4655_ = lean_array_get_size(v_buckets_4575_);
                    v___x_4656_ = lean_nat_dec_lt(v___x_4566_, v___x_4655_);
                    if v___x_4656_ == 0 {
                        leanh::lean_dec_ref(v_buckets_4575_);
                        v___y_4640_ = v___x_4654_;
                        state = 17;
                        continue;
                    } else {
                        v___x_4657_ = lean_nat_dec_le(v___x_4655_, v___x_4655_);
                        if v___x_4657_ == 0 {
                            if v___x_4656_ == 0 {
                                leanh::lean_dec_ref(v_buckets_4575_);
                                v___y_4640_ = v___x_4654_;
                                state = 17;
                                continue;
                            } else {
                                v___x_4658_ = 0usize;
                                v___x_4659_ = lean_usize_of_nat(v___x_4655_);
                                v___x_4660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_4575_, v___x_4658_, v___x_4659_, v___x_4654_);
                                leanh::lean_dec_ref(v_buckets_4575_);
                                v___y_4640_ = v___x_4660_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v___x_4661_ = 0usize;
                            v___x_4662_ = lean_usize_of_nat(v___x_4655_);
                            v___x_4663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_4575_, v___x_4661_, v___x_4662_, v___x_4654_);
                            leanh::lean_dec_ref(v_buckets_4575_);
                            v___y_4640_ = v___x_4663_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_buckets_4575_);
                    leanh::lean_dec(v_size_4574_);
                    v___x_4664_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4538_);
                    if leanh::lean_obj_tag(v___x_4664_) == 0 {
                        v_a_4665_ = leanh::lean_ctor_get(v___x_4664_, 0);
                        leanh::lean_inc(v_a_4665_);
                        leanh::lean_dec_ref_known(v___x_4664_, 1);
                        v___x_4666_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4540_);
                        if leanh::lean_obj_tag(v___x_4666_) == 0 {
                            v_a_4667_ = leanh::lean_ctor_get(v___x_4666_, 0);
                            v_isSharedCheck_4706_ =
                                (!leanh::lean_is_exclusive(v___x_4666_)) as u8;
                            if v_isSharedCheck_4706_ == 0 {
                                v___x_4669_ = v___x_4666_;
                                v_isShared_4670_ = v_isSharedCheck_4706_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4667_);
                                leanh::lean_dec(v___x_4666_);
                                v___x_4669_ = leanh::lean_box(0);
                                v_isShared_4670_ = v_isSharedCheck_4706_;
                                state = 19;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4665_);
                            leanh::lean_del_object(v___x_4648_);
                            leanh::lean_del_object(v___x_4577_);
                            v_a_4707_ = leanh::lean_ctor_get(v___x_4666_, 0);
                            v_isSharedCheck_4714_ =
                                (!leanh::lean_is_exclusive(v___x_4666_)) as u8;
                            if v_isSharedCheck_4714_ == 0 {
                                v___x_4709_ = v___x_4666_;
                                v_isShared_4710_ = v_isSharedCheck_4714_;
                                state = 27;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4707_);
                                leanh::lean_dec(v___x_4666_);
                                v___x_4709_ = leanh::lean_box(0);
                                v_isShared_4710_ = v_isSharedCheck_4714_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_4648_);
                        leanh::lean_del_object(v___x_4577_);
                        v_a_4715_ = leanh::lean_ctor_get(v___x_4664_, 0);
                        v_isSharedCheck_4722_ =
                            (!leanh::lean_is_exclusive(v___x_4664_)) as u8;
                        if v_isSharedCheck_4722_ == 0 {
                            v___x_4717_ = v___x_4664_;
                            v_isShared_4718_ = v_isSharedCheck_4722_;
                            state = 29;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4715_);
                            leanh::lean_dec(v___x_4664_);
                            v___x_4717_ = leanh::lean_box(0);
                            v_isShared_4718_ = v_isSharedCheck_4722_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            19 => {
                v___x_4671_ = (leanh::lean_unbox(v_a_4667_) as u8);
                leanh::lean_dec(v_a_4667_);
                if v___x_4671_ == 0 {
                    leanh::lean_dec(v_a_4665_);
                    leanh::lean_del_object(v___x_4648_);
                    leanh::lean_del_object(v___x_4577_);
                    v___x_4672_ = leanh::lean_box((v___x_4579_) as usize);
                    if v_isShared_4670_ == 0 {
                        leanh::lean_ctor_set(v___x_4669_, 0, v___x_4672_);
                        v___x_4674_ = v___x_4669_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_4675_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4672_);
                        v___x_4674_ = v_reuseFailAlloc_4675_;
                        state = 20;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4669_);
                    v_splits_4676_ = leanh::lean_ctor_get(v_a_4665_, 0);
                    leanh::lean_inc(v_splits_4676_);
                    leanh::lean_dec(v_a_4665_);
                    v___x_4677_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__4_once),
                        _init_l_Lean_Meta_Grind_mbtc___closed__4,
                    );
                    v___x_4678_ = l_Nat_reprFast(v_splits_4676_);
                    v___x_4679_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4679_, 0, v___x_4678_);
                    v___x_4680_ = l_Lean_MessageData_ofFormat(v___x_4679_);
                    if v_isShared_4649_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4648_, 7);
                        leanh::lean_ctor_set(v___x_4648_, 1, v___x_4680_);
                        leanh::lean_ctor_set(v___x_4648_, 0, v___x_4677_);
                        v___x_4682_ = v___x_4648_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_4705_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 0, v___x_4677_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 1, v___x_4680_);
                        v___x_4682_ = v_reuseFailAlloc_4705_;
                        state = 21;
                        continue;
                    }
                }
            }
            20 => {
                return v___x_4674_;
            }
            21 => {
                v___x_4683_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__6_once),
                    _init_l_Lean_Meta_Grind_mbtc___closed__6,
                );
                if v_isShared_4578_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4577_, 7);
                    leanh::lean_ctor_set(v___x_4577_, 1, v___x_4683_);
                    leanh::lean_ctor_set(v___x_4577_, 0, v___x_4682_);
                    v___x_4685_ = v___x_4577_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4704_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4682_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 1, v___x_4683_);
                    v___x_4685_ = v_reuseFailAlloc_4704_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_4686_ = l_Lean_Meta_Sym_reportIssue(
                    v___x_4685_,
                    v_a_4540_,
                    v_a_4541_,
                    v_a_4542_,
                    v_a_4543_,
                    v_a_4544_,
                    v_a_4545_,
                );
                if leanh::lean_obj_tag(v___x_4686_) == 0 {
                    v_isSharedCheck_4694_ = (!leanh::lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4694_ == 0 {
                        v_unused_4695_ = leanh::lean_ctor_get(v___x_4686_, 0);
                        leanh::lean_dec(v_unused_4695_);
                        v___x_4688_ = v___x_4686_;
                        v_isShared_4689_ = v_isSharedCheck_4694_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4686_);
                        v___x_4688_ = leanh::lean_box(0);
                        v_isShared_4689_ = v_isSharedCheck_4694_;
                        state = 23;
                        continue;
                    }
                } else {
                    v_a_4696_ = leanh::lean_ctor_get(v___x_4686_, 0);
                    v_isSharedCheck_4703_ = (!leanh::lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4703_ == 0 {
                        v___x_4698_ = v___x_4686_;
                        v_isShared_4699_ = v_isSharedCheck_4703_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4696_);
                        leanh::lean_dec(v___x_4686_);
                        v___x_4698_ = leanh::lean_box(0);
                        v_isShared_4699_ = v_isSharedCheck_4703_;
                        state = 25;
                        continue;
                    }
                }
            }
            23 => {
                v___x_4690_ = leanh::lean_box((v___x_4579_) as usize);
                if v_isShared_4689_ == 0 {
                    leanh::lean_ctor_set(v___x_4688_, 0, v___x_4690_);
                    v___x_4692_ = v___x_4688_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4690_);
                    v___x_4692_ = v_reuseFailAlloc_4693_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4692_;
            }
            25 => {
                if v_isShared_4699_ == 0 {
                    v___x_4701_ = v___x_4698_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4702_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_a_4696_);
                    v___x_4701_ = v_reuseFailAlloc_4702_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4701_;
            }
            27 => {
                if v_isShared_4710_ == 0 {
                    v___x_4712_ = v___x_4709_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4713_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
                    v___x_4712_ = v_reuseFailAlloc_4713_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4712_;
            }
            29 => {
                if v_isShared_4718_ == 0 {
                    v___x_4720_ = v___x_4717_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4721_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4715_);
                    v___x_4720_ = v_reuseFailAlloc_4721_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4720_;
            }
            31 => {
                if v_isShared_4728_ == 0 {
                    v___x_4730_ = v___x_4727_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4731_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4725_);
                    v___x_4730_ = v_reuseFailAlloc_4731_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4730_;
            }
            33 => {
                return v___x_4734_;
            }
            34 => {
                if v_isShared_4741_ == 0 {
                    v___x_4743_ = v___x_4740_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4744_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
                    v___x_4743_ = v_reuseFailAlloc_4744_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4743_;
            }
            36 => {
                return v___x_4749_;
            }
            37 => {
                if v_isShared_4756_ == 0 {
                    v___x_4758_ = v___x_4755_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
                    v___x_4758_ = v_reuseFailAlloc_4759_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mbtc___boxed(
    mut v_ctx_4761_: *mut leanh::LeanObject,
    mut v_a_4762_: *mut leanh::LeanObject,
    mut v_a_4763_: *mut leanh::LeanObject,
    mut v_a_4764_: *mut leanh::LeanObject,
    mut v_a_4765_: *mut leanh::LeanObject,
    mut v_a_4766_: *mut leanh::LeanObject,
    mut v_a_4767_: *mut leanh::LeanObject,
    mut v_a_4768_: *mut leanh::LeanObject,
    mut v_a_4769_: *mut leanh::LeanObject,
    mut v_a_4770_: *mut leanh::LeanObject,
    mut v_a_4771_: *mut leanh::LeanObject,
    mut v_a_4772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4773_ = l_Lean_Meta_Grind_mbtc(
        v_ctx_4761_,
        v_a_4762_,
        v_a_4763_,
        v_a_4764_,
        v_a_4765_,
        v_a_4766_,
        v_a_4767_,
        v_a_4768_,
        v_a_4769_,
        v_a_4770_,
        v_a_4771_,
    );
    leanh::lean_dec(v_a_4771_);
    leanh::lean_dec_ref(v_a_4770_);
    leanh::lean_dec(v_a_4769_);
    leanh::lean_dec_ref(v_a_4768_);
    leanh::lean_dec(v_a_4767_);
    leanh::lean_dec_ref(v_a_4766_);
    leanh::lean_dec(v_a_4765_);
    leanh::lean_dec_ref(v_a_4764_);
    leanh::lean_dec(v_a_4763_);
    leanh::lean_dec(v_a_4762_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(
    mut v_cls_4774_: *mut leanh::LeanObject,
    mut v_msg_4775_: *mut leanh::LeanObject,
    mut v___y_4776_: *mut leanh::LeanObject,
    mut v___y_4777_: *mut leanh::LeanObject,
    mut v___y_4778_: *mut leanh::LeanObject,
    mut v___y_4779_: *mut leanh::LeanObject,
    mut v___y_4780_: *mut leanh::LeanObject,
    mut v___y_4781_: *mut leanh::LeanObject,
    mut v___y_4782_: *mut leanh::LeanObject,
    mut v___y_4783_: *mut leanh::LeanObject,
    mut v___y_4784_: *mut leanh::LeanObject,
    mut v___y_4785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4787_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(
        v_cls_4774_,
        v_msg_4775_,
        v___y_4782_,
        v___y_4783_,
        v___y_4784_,
        v___y_4785_,
    );
    return v___x_4787_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___boxed(
    mut v_cls_4788_: *mut leanh::LeanObject,
    mut v_msg_4789_: *mut leanh::LeanObject,
    mut v___y_4790_: *mut leanh::LeanObject,
    mut v___y_4791_: *mut leanh::LeanObject,
    mut v___y_4792_: *mut leanh::LeanObject,
    mut v___y_4793_: *mut leanh::LeanObject,
    mut v___y_4794_: *mut leanh::LeanObject,
    mut v___y_4795_: *mut leanh::LeanObject,
    mut v___y_4796_: *mut leanh::LeanObject,
    mut v___y_4797_: *mut leanh::LeanObject,
    mut v___y_4798_: *mut leanh::LeanObject,
    mut v___y_4799_: *mut leanh::LeanObject,
    mut v___y_4800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4801_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(
        v_cls_4788_,
        v_msg_4789_,
        v___y_4790_,
        v___y_4791_,
        v___y_4792_,
        v___y_4793_,
        v___y_4794_,
        v___y_4795_,
        v___y_4796_,
        v___y_4797_,
        v___y_4798_,
        v___y_4799_,
    );
    leanh::lean_dec(v___y_4799_);
    leanh::lean_dec_ref(v___y_4798_);
    leanh::lean_dec(v___y_4797_);
    leanh::lean_dec_ref(v___y_4796_);
    leanh::lean_dec(v___y_4795_);
    leanh::lean_dec_ref(v___y_4794_);
    leanh::lean_dec(v___y_4793_);
    leanh::lean_dec_ref(v___y_4792_);
    leanh::lean_dec(v___y_4791_);
    leanh::lean_dec(v___y_4790_);
    return v_res_4801_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(
    mut v_00_u03b2_4802_: *mut leanh::LeanObject,
    mut v_m_4803_: *mut leanh::LeanObject,
    mut v_a_4804_: *mut leanh::LeanObject,
    mut v_b_4805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4806_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_4803_, v_a_4804_, v_b_4805_);
    return v___x_4806_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(
    mut v_00_u03b2_4807_: *mut leanh::LeanObject,
    mut v_m_4808_: *mut leanh::LeanObject,
    mut v_a_4809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_4808_, v_a_4809_);
    return v___x_4810_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(
    mut v_00_u03b2_4811_: *mut leanh::LeanObject,
    mut v_m_4812_: *mut leanh::LeanObject,
    mut v_a_4813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4814_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(
            v_00_u03b2_4811_,
            v_m_4812_,
            v_a_4813_,
        );
    leanh::lean_dec_ref(v_a_4813_);
    leanh::lean_dec_ref(v_m_4812_);
    return v_res_4814_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(
    mut v_ctx_4815_: *mut leanh::LeanObject,
    mut v_val_4816_: *mut leanh::LeanObject,
    mut v___x_4817_: *mut leanh::LeanObject,
    mut v___x_4818_: *mut leanh::LeanObject,
    mut v_as_4819_: *mut leanh::LeanObject,
    mut v_as_x27_4820_: *mut leanh::LeanObject,
    mut v_b_4821_: *mut leanh::LeanObject,
    mut v_a_4822_: *mut leanh::LeanObject,
    mut v___y_4823_: *mut leanh::LeanObject,
    mut v___y_4824_: *mut leanh::LeanObject,
    mut v___y_4825_: *mut leanh::LeanObject,
    mut v___y_4826_: *mut leanh::LeanObject,
    mut v___y_4827_: *mut leanh::LeanObject,
    mut v___y_4828_: *mut leanh::LeanObject,
    mut v___y_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
    mut v___y_4831_: *mut leanh::LeanObject,
    mut v___y_4832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4834_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(
        v_ctx_4815_,
        v_val_4816_,
        v___x_4817_,
        v___x_4818_,
        v_as_x27_4820_,
        v_b_4821_,
        v___y_4823_,
        v___y_4824_,
        v___y_4825_,
        v___y_4826_,
        v___y_4827_,
        v___y_4828_,
        v___y_4829_,
        v___y_4830_,
        v___y_4831_,
        v___y_4832_,
    );
    return v___x_4834_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctx_4835_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_val_4836_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_4837_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_4838_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_as_4839_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_as_x27_4840_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_b_4841_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_a_4842_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4843_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4844_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4845_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4846_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4847_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4848_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4849_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4850_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4851_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4852_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_4853_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_res_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4854_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(
        v_ctx_4835_,
        v_val_4836_,
        v___x_4837_,
        v___x_4838_,
        v_as_4839_,
        v_as_x27_4840_,
        v_b_4841_,
        v_a_4842_,
        v___y_4843_,
        v___y_4844_,
        v___y_4845_,
        v___y_4846_,
        v___y_4847_,
        v___y_4848_,
        v___y_4849_,
        v___y_4850_,
        v___y_4851_,
        v___y_4852_,
    );
    leanh::lean_dec(v___y_4852_);
    leanh::lean_dec_ref(v___y_4851_);
    leanh::lean_dec(v___y_4850_);
    leanh::lean_dec_ref(v___y_4849_);
    leanh::lean_dec(v___y_4848_);
    leanh::lean_dec_ref(v___y_4847_);
    leanh::lean_dec(v___y_4846_);
    leanh::lean_dec_ref(v___y_4845_);
    leanh::lean_dec(v___y_4844_);
    leanh::lean_dec(v___y_4843_);
    leanh::lean_dec(v_as_x27_4840_);
    leanh::lean_dec(v_as_4839_);
    return v_res_4854_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(
    mut v_00_u03b2_4855_: *mut leanh::LeanObject,
    mut v_m_4856_: *mut leanh::LeanObject,
    mut v_a_4857_: *mut leanh::LeanObject,
    mut v_b_4858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4859_ =
        l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(
            v_m_4856_, v_a_4857_, v_b_4858_,
        );
    return v___x_4859_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(
    mut v_n_4860_: *mut leanh::LeanObject,
    mut v_as_4861_: *mut leanh::LeanObject,
    mut v_lo_4862_: *mut leanh::LeanObject,
    mut v_hi_4863_: *mut leanh::LeanObject,
    mut v_w_4864_: *mut leanh::LeanObject,
    mut v_hlo_4865_: *mut leanh::LeanObject,
    mut v_hhi_4866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4867_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_4860_, v_as_4861_, v_lo_4862_, v_hi_4863_);
    return v___x_4867_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(
    mut v_n_4868_: *mut leanh::LeanObject,
    mut v_as_4869_: *mut leanh::LeanObject,
    mut v_lo_4870_: *mut leanh::LeanObject,
    mut v_hi_4871_: *mut leanh::LeanObject,
    mut v_w_4872_: *mut leanh::LeanObject,
    mut v_hlo_4873_: *mut leanh::LeanObject,
    mut v_hhi_4874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4875_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_4868_, v_as_4869_, v_lo_4870_, v_hi_4871_, v_w_4872_, v_hlo_4873_, v_hhi_4874_);
    leanh::lean_dec(v_hi_4871_);
    leanh::lean_dec(v_n_4868_);
    return v_res_4875_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(
    mut v_00_u03b2_4876_: *mut leanh::LeanObject,
    mut v_a_4877_: *mut leanh::LeanObject,
    mut v_x_4878_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4879_: u8 = 0;
    v___x_4879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_4877_, v_x_4878_);
    return v___x_4879_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(
    mut v_00_u03b2_4880_: *mut leanh::LeanObject,
    mut v_a_4881_: *mut leanh::LeanObject,
    mut v_x_4882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4883_: u8 = 0;
    let mut v_r_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4883_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_4880_, v_a_4881_, v_x_4882_);
    leanh::lean_dec(v_x_4882_);
    leanh::lean_dec_ref(v_a_4881_);
    v_r_4884_ = leanh::lean_box((v_res_4883_) as usize);
    return v_r_4884_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(
    mut v_00_u03b2_4885_: *mut leanh::LeanObject,
    mut v_data_4886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4887_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_4886_);
    return v___x_4887_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(
    mut v_00_u03b2_4888_: *mut leanh::LeanObject,
    mut v_a_4889_: *mut leanh::LeanObject,
    mut v_x_4890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4891_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_4889_, v_x_4890_);
    return v___x_4891_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(
    mut v_00_u03b2_4892_: *mut leanh::LeanObject,
    mut v_a_4893_: *mut leanh::LeanObject,
    mut v_x_4894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4895_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_4892_, v_a_4893_, v_x_4894_);
    leanh::lean_dec(v_x_4894_);
    leanh::lean_dec_ref(v_a_4893_);
    return v_res_4895_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(
    mut v_00_u03b2_4896_: *mut leanh::LeanObject,
    mut v_a_4897_: *mut leanh::LeanObject,
    mut v_x_4898_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4899_: u8 = 0;
    v___x_4899_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_4897_, v_x_4898_);
    return v___x_4899_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(
    mut v_00_u03b2_4900_: *mut leanh::LeanObject,
    mut v_a_4901_: *mut leanh::LeanObject,
    mut v_x_4902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4903_: u8 = 0;
    let mut v_r_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4903_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_4900_, v_a_4901_, v_x_4902_);
    leanh::lean_dec(v_x_4902_);
    leanh::lean_dec_ref(v_a_4901_);
    v_r_4904_ = leanh::lean_box((v_res_4903_) as usize);
    return v_r_4904_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(
    mut v_00_u03b2_4905_: *mut leanh::LeanObject,
    mut v_data_4906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4907_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_4906_);
    return v___x_4907_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(
    mut v_00_u03b2_4908_: *mut leanh::LeanObject,
    mut v_a_4909_: *mut leanh::LeanObject,
    mut v_b_4910_: *mut leanh::LeanObject,
    mut v_x_4911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4912_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_4909_, v_b_4910_, v_x_4911_);
    return v___x_4912_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(
    mut v_n_4913_: *mut leanh::LeanObject,
    mut v_lo_4914_: *mut leanh::LeanObject,
    mut v_hi_4915_: *mut leanh::LeanObject,
    mut v_hhi_4916_: *mut leanh::LeanObject,
    mut v_pivot_4917_: *mut leanh::LeanObject,
    mut v_as_4918_: *mut leanh::LeanObject,
    mut v_i_4919_: *mut leanh::LeanObject,
    mut v_k_4920_: *mut leanh::LeanObject,
    mut v_ilo_4921_: *mut leanh::LeanObject,
    mut v_ik_4922_: *mut leanh::LeanObject,
    mut v_w_4923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4924_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_4915_, v_pivot_4917_, v_as_4918_, v_i_4919_, v_k_4920_);
    return v___x_4924_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(
    mut v_n_4925_: *mut leanh::LeanObject,
    mut v_lo_4926_: *mut leanh::LeanObject,
    mut v_hi_4927_: *mut leanh::LeanObject,
    mut v_hhi_4928_: *mut leanh::LeanObject,
    mut v_pivot_4929_: *mut leanh::LeanObject,
    mut v_as_4930_: *mut leanh::LeanObject,
    mut v_i_4931_: *mut leanh::LeanObject,
    mut v_k_4932_: *mut leanh::LeanObject,
    mut v_ilo_4933_: *mut leanh::LeanObject,
    mut v_ik_4934_: *mut leanh::LeanObject,
    mut v_w_4935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4936_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_4925_, v_lo_4926_, v_hi_4927_, v_hhi_4928_, v_pivot_4929_, v_as_4930_, v_i_4931_, v_k_4932_, v_ilo_4933_, v_ik_4934_, v_w_4935_);
    leanh::lean_dec_ref(v_pivot_4929_);
    leanh::lean_dec(v_hi_4927_);
    leanh::lean_dec(v_lo_4926_);
    leanh::lean_dec(v_n_4925_);
    return v_res_4936_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(
    mut v_00_u03b2_4937_: *mut leanh::LeanObject,
    mut v_i_4938_: *mut leanh::LeanObject,
    mut v_source_4939_: *mut leanh::LeanObject,
    mut v_target_4940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4941_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_4938_, v_source_4939_, v_target_4940_);
    return v___x_4941_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(
    mut v_00_u03b2_4942_: *mut leanh::LeanObject,
    mut v_i_4943_: *mut leanh::LeanObject,
    mut v_source_4944_: *mut leanh::LeanObject,
    mut v_target_4945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4946_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_4943_, v_source_4944_, v_target_4945_);
    return v___x_4946_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(
    mut v_00_u03b2_4947_: *mut leanh::LeanObject,
    mut v_x_4948_: *mut leanh::LeanObject,
    mut v_x_4949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4950_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_4948_, v_x_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(
    mut v_00_u03b2_4951_: *mut leanh::LeanObject,
    mut v_x_4952_: *mut leanh::LeanObject,
    mut v_x_4953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4954_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_4952_, v_x_4953_);
    return v___x_4954_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark =
        _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark,
    );
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark =
        _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_MBTC(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_MBTC(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
}
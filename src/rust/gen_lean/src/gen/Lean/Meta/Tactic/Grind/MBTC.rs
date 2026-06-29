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
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
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
        95, 95, 103, 114, 105, 110, 100, 95, 109, 97, 105, 110, 95, 97, 114, 103, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1_value:
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
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        4700630907035917417 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [95, 95, 103, 114, 105, 110, 100, 95, 111, 116, 104, 101, 114, 95, 97, 114, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__0_value) as *mut crate::leanh::LeanObject,18094379780977335043 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 98, 116, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__1_value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,15448887498159686406 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__4_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 64, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__2_value) as *mut crate::leanh::LeanObject,3746410129963432689 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value:
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
static mut l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mbtc___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mbtc___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_mbtc___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mbtc___closed__3_value: crate::leanh::LeanStringObject<72> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mbtc___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mbtc___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mbtc___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mbtc___closed__5_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mbtc___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mbtc___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mbtc___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mbtc___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(
    mut v_x_2478_: *mut crate::leanh::LeanObject,
    mut v_x_2479_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2480_: u8 = 0;
    v___x_2480_ = lean_expr_eqv(v_x_2478_, v_x_2479_);
    return v___x_2480_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq___boxed(
    mut v_x_2481_: *mut crate::leanh::LeanObject,
    mut v_x_2482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2483_: u8 = 0;
    let mut v_r_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2483_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instBEqKey_beq(
        v_x_2481_, v_x_2482_,
    );
    crate::leanh::lean_dec_ref(v_x_2482_);
    crate::leanh::lean_dec_ref(v_x_2481_);
    v_r_2484_ = crate::leanh::lean_box((v_res_2483_) as usize);
    return v_r_2484_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(
    mut v_x_2487_: *mut crate::leanh::LeanObject,
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
    mut v_x_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2492_: u64 = 0;
    let mut v_r_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2492_ =
        l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_instHashableKey_hash(v_x_2491_);
    crate::leanh::lean_dec_ref(v_x_2491_);
    v_r_2493_ = crate::leanh::lean_box_uint64(v_res_2492_);
    return v_r_2493_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2499_ = crate::leanh::lean_box(0);
    v___x_2500_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark___closed__1;
    v___x_2501_ = l_Lean_mkConst(v___x_2500_, v___x_2499_);
    return v___x_2501_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2502_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2506_ = crate::leanh::lean_box(0);
    v___x_2507_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark___closed__1;
    v___x_2508_ = l_Lean_mkConst(v___x_2507_, v___x_2506_);
    return v___x_2508_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2509_ = crate::leanh::lean_obj_once(
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
    mut v_upperBound_2510_: *mut crate::leanh::LeanObject,
    mut v_i_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
    mut v_b_2514_: *mut crate::leanh::LeanObject,
    mut v___y_2515_: *mut crate::leanh::LeanObject,
    mut v___y_2516_: *mut crate::leanh::LeanObject,
    mut v___y_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: u8 = 0;
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: u8 = 0;
    let mut v_paramInfo_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v_a_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2539_: u8 = 0;
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2543_: u8 = 0;
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2525_ = lean_nat_dec_lt(v_a_2513_, v_upperBound_2510_);
                if v___x_2525_ == 0 {
                    crate::leanh::lean_dec(v_a_2513_);
                    v___x_2526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2526_, 0, v_b_2514_);
                    return v___x_2526_;
                } else {
                    v___x_2527_ = lean_nat_dec_eq(v_i_2511_, v_a_2513_);
                    if v___x_2527_ == 0 {
                        v_paramInfo_2528_ = crate::leanh::lean_ctor_get(v_a_2512_, 0);
                        v___x_2529_ = lean_array_fget_borrowed(v_b_2514_, v_a_2513_);
                        crate::leanh::lean_inc(v___x_2529_);
                        v___x_2530_ = l_Lean_Meta_Sym_Canon_isSupport(
                            v_paramInfo_2528_,
                            v_a_2513_,
                            v___x_2529_,
                            v___y_2515_,
                            v___y_2516_,
                            v___y_2517_,
                            v___y_2518_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2530_) == 0 {
                            v_a_2531_ = crate::leanh::lean_ctor_get(v___x_2530_, 0);
                            crate::leanh::lean_inc(v_a_2531_);
                            crate::leanh::lean_dec_ref_known(v___x_2530_, 1);
                            v___x_2535_ = (crate::leanh::lean_unbox(v_a_2531_) as u8);
                            crate::leanh::lean_dec(v_a_2531_);
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
                            crate::leanh::lean_dec_ref(v_b_2514_);
                            crate::leanh::lean_dec(v_a_2513_);
                            v_a_2536_ = crate::leanh::lean_ctor_get(v___x_2530_, 0);
                            v_isSharedCheck_2543_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2530_)) as u8;
                            if v_isSharedCheck_2543_ == 0 {
                                v___x_2538_ = v___x_2530_;
                                v_isShared_2539_ = v_isSharedCheck_2543_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2536_);
                                crate::leanh::lean_dec(v___x_2530_);
                                v___x_2538_ = crate::leanh::lean_box(0);
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
                v___x_2522_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2523_ = lean_nat_add(v_a_2513_, v___x_2522_);
                crate::leanh::lean_dec(v_a_2513_);
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
                    v_reuseFailAlloc_2542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
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
    mut v_upperBound_2546_: *mut crate::leanh::LeanObject,
    mut v_i_2547_: *mut crate::leanh::LeanObject,
    mut v_a_2548_: *mut crate::leanh::LeanObject,
    mut v_a_2549_: *mut crate::leanh::LeanObject,
    mut v_b_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_2546_, v_i_2547_, v_a_2548_, v_a_2549_, v_b_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
    crate::leanh::lean_dec(v___y_2554_);
    crate::leanh::lean_dec_ref(v___y_2553_);
    crate::leanh::lean_dec(v___y_2552_);
    crate::leanh::lean_dec_ref(v___y_2551_);
    crate::leanh::lean_dec_ref(v_a_2548_);
    crate::leanh::lean_dec(v_i_2547_);
    crate::leanh::lean_dec(v_upperBound_2546_);
    return v_res_2556_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(
    mut v_i_2557_: *mut crate::leanh::LeanObject,
    mut v_x_2558_: *mut crate::leanh::LeanObject,
    mut v_x_2559_: *mut crate::leanh::LeanObject,
    mut v_x_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
    mut v___y_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2581_: u8 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v_a_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2590_: u8 = 0;
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2594_: u8 = 0;
    let mut v_a_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2558_) == 5 {
                    v_fn_2566_ = crate::leanh::lean_ctor_get(v_x_2558_, 0);
                    crate::leanh::lean_inc_ref(v_fn_2566_);
                    v_arg_2567_ = crate::leanh::lean_ctor_get(v_x_2558_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2567_);
                    crate::leanh::lean_dec_ref_known(v_x_2558_, 2);
                    v___x_2568_ = lean_array_set(v_x_2559_, v_x_2560_, v_arg_2567_);
                    v___x_2569_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2570_ = lean_nat_sub(v_x_2560_, v___x_2569_);
                    crate::leanh::lean_dec(v_x_2560_);
                    v_x_2558_ = v_fn_2566_;
                    v_x_2559_ = v___x_2568_;
                    v_x_2560_ = v___x_2570_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_2560_);
                    v___x_2572_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_x_2558_);
                    v___x_2573_ = l_Lean_Meta_getFunInfo(
                        v_x_2558_,
                        v___x_2572_,
                        v___y_2561_,
                        v___y_2562_,
                        v___y_2563_,
                        v___y_2564_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2573_) == 0 {
                        v_a_2574_ = crate::leanh::lean_ctor_get(v___x_2573_, 0);
                        crate::leanh::lean_inc(v_a_2574_);
                        crate::leanh::lean_dec_ref_known(v___x_2573_, 1);
                        v___x_2575_ = lean_array_get_size(v_x_2559_);
                        v___x_2576_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2577_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v___x_2575_, v_i_2557_, v_a_2574_, v___x_2576_, v_x_2559_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
                        crate::leanh::lean_dec(v_a_2574_);
                        if crate::leanh::lean_obj_tag(v___x_2577_) == 0 {
                            v_a_2578_ = crate::leanh::lean_ctor_get(v___x_2577_, 0);
                            v_isSharedCheck_2586_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2577_)) as u8;
                            if v_isSharedCheck_2586_ == 0 {
                                v___x_2580_ = v___x_2577_;
                                v_isShared_2581_ = v_isSharedCheck_2586_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2578_);
                                crate::leanh::lean_dec(v___x_2577_);
                                v___x_2580_ = crate::leanh::lean_box(0);
                                v_isShared_2581_ = v_isSharedCheck_2586_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_x_2558_);
                            v_a_2587_ = crate::leanh::lean_ctor_get(v___x_2577_, 0);
                            v_isSharedCheck_2594_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2577_)) as u8;
                            if v_isSharedCheck_2594_ == 0 {
                                v___x_2589_ = v___x_2577_;
                                v_isShared_2590_ = v_isSharedCheck_2594_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2587_);
                                crate::leanh::lean_dec(v___x_2577_);
                                v___x_2589_ = crate::leanh::lean_box(0);
                                v_isShared_2590_ = v_isSharedCheck_2594_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_2559_);
                        crate::leanh::lean_dec_ref(v_x_2558_);
                        v_a_2595_ = crate::leanh::lean_ctor_get(v___x_2573_, 0);
                        v_isSharedCheck_2602_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2573_)) as u8;
                        if v_isSharedCheck_2602_ == 0 {
                            v___x_2597_ = v___x_2573_;
                            v_isShared_2598_ = v_isSharedCheck_2602_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2595_);
                            crate::leanh::lean_dec(v___x_2573_);
                            v___x_2597_ = crate::leanh::lean_box(0);
                            v_isShared_2598_ = v_isSharedCheck_2602_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2582_ = l_Lean_mkAppN(v_x_2558_, v_a_2578_);
                crate::leanh::lean_dec(v_a_2578_);
                if v_isShared_2581_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2580_, 0, v___x_2582_);
                    v___x_2584_ = v___x_2580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
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
                    v_reuseFailAlloc_2593_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
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
                    v_reuseFailAlloc_2601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
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
    mut v_i_2603_: *mut crate::leanh::LeanObject,
    mut v_x_2604_: *mut crate::leanh::LeanObject,
    mut v_x_2605_: *mut crate::leanh::LeanObject,
    mut v_x_2606_: *mut crate::leanh::LeanObject,
    mut v___y_2607_: *mut crate::leanh::LeanObject,
    mut v___y_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
    mut v___y_2610_: *mut crate::leanh::LeanObject,
    mut v___y_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2612_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_2603_, v_x_2604_, v_x_2605_, v_x_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
    crate::leanh::lean_dec(v___y_2610_);
    crate::leanh::lean_dec_ref(v___y_2609_);
    crate::leanh::lean_dec(v___y_2608_);
    crate::leanh::lean_dec_ref(v___y_2607_);
    crate::leanh::lean_dec(v_i_2603_);
    return v_res_2612_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = crate::leanh::lean_box(0);
    v_dummy_2614_ = l_Lean_Expr_sort___override(v___x_2613_);
    return v_dummy_2614_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(
    mut v_e_2615_: *mut crate::leanh::LeanObject,
    mut v_i_2616_: *mut crate::leanh::LeanObject,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_2622_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0,
    );
    v_nargs_2623_ = l_Lean_Expr_getAppNumArgs(v_e_2615_);
    crate::leanh::lean_inc(v_nargs_2623_);
    v___x_2624_ = lean_mk_array(v_nargs_2623_, v_dummy_2622_);
    v___x_2625_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2626_ = lean_nat_sub(v_nargs_2623_, v___x_2625_);
    crate::leanh::lean_dec(v_nargs_2623_);
    v___x_2627_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__1(v_i_2616_, v_e_2615_, v___x_2624_, v___x_2626_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
    return v___x_2627_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___boxed(
    mut v_e_2628_: *mut crate::leanh::LeanObject,
    mut v_i_2629_: *mut crate::leanh::LeanObject,
    mut v_a_2630_: *mut crate::leanh::LeanObject,
    mut v_a_2631_: *mut crate::leanh::LeanObject,
    mut v_a_2632_: *mut crate::leanh::LeanObject,
    mut v_a_2633_: *mut crate::leanh::LeanObject,
    mut v_a_2634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2635_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(
        v_e_2628_, v_i_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_,
    );
    crate::leanh::lean_dec(v_a_2633_);
    crate::leanh::lean_dec_ref(v_a_2632_);
    crate::leanh::lean_dec(v_a_2631_);
    crate::leanh::lean_dec_ref(v_a_2630_);
    crate::leanh::lean_dec(v_i_2629_);
    return v_res_2635_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(
    mut v_upperBound_2636_: *mut crate::leanh::LeanObject,
    mut v_i_2637_: *mut crate::leanh::LeanObject,
    mut v_a_2638_: *mut crate::leanh::LeanObject,
    mut v___x_2639_: *mut crate::leanh::LeanObject,
    mut v_inst_2640_: *mut crate::leanh::LeanObject,
    mut v_R_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
    mut v_b_2643_: *mut crate::leanh::LeanObject,
    mut v_c_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
    mut v___y_2648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2650_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___redArg(v_upperBound_2636_, v_i_2637_, v_a_2638_, v_a_2642_, v_b_2643_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
    return v___x_2650_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0___boxed(
    mut v_upperBound_2651_: *mut crate::leanh::LeanObject,
    mut v_i_2652_: *mut crate::leanh::LeanObject,
    mut v_a_2653_: *mut crate::leanh::LeanObject,
    mut v___x_2654_: *mut crate::leanh::LeanObject,
    mut v_inst_2655_: *mut crate::leanh::LeanObject,
    mut v_R_2656_: *mut crate::leanh::LeanObject,
    mut v_a_2657_: *mut crate::leanh::LeanObject,
    mut v_b_2658_: *mut crate::leanh::LeanObject,
    mut v_c_2659_: *mut crate::leanh::LeanObject,
    mut v___y_2660_: *mut crate::leanh::LeanObject,
    mut v___y_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey_spec__0(v_upperBound_2651_, v_i_2652_, v_a_2653_, v___x_2654_, v_inst_2655_, v_R_2656_, v_a_2657_, v_b_2658_, v_c_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
    crate::leanh::lean_dec(v___y_2663_);
    crate::leanh::lean_dec_ref(v___y_2662_);
    crate::leanh::lean_dec(v___y_2661_);
    crate::leanh::lean_dec_ref(v___y_2660_);
    crate::leanh::lean_dec(v___x_2654_);
    crate::leanh::lean_dec_ref(v_a_2653_);
    crate::leanh::lean_dec(v_i_2652_);
    crate::leanh::lean_dec(v_upperBound_2651_);
    return v_res_2665_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_b_2667_: *mut crate::leanh::LeanObject,
    mut v_i_2668_: *mut crate::leanh::LeanObject,
    mut v_a_2669_: *mut crate::leanh::LeanObject,
    mut v_a_2670_: *mut crate::leanh::LeanObject,
    mut v_a_2671_: *mut crate::leanh::LeanObject,
    mut v_a_2672_: *mut crate::leanh::LeanObject,
    mut v_a_2673_: *mut crate::leanh::LeanObject,
    mut v_a_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_arg_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_app_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_app_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2691_: u8 = 0;
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_a_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut v_a_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut v_a_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2717_: u8 = 0;
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2721_: u8 = 0;
    let mut v___x_2722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_arg_2676_ = crate::leanh::lean_ctor_get(v_a_2666_, 0);
                crate::leanh::lean_inc_ref(v_arg_2676_);
                v_app_2677_ = crate::leanh::lean_ctor_get(v_a_2666_, 1);
                crate::leanh::lean_inc_ref(v_app_2677_);
                crate::leanh::lean_dec_ref(v_a_2666_);
                v_arg_2678_ = crate::leanh::lean_ctor_get(v_b_2667_, 0);
                crate::leanh::lean_inc_ref(v_arg_2678_);
                v_app_2679_ = crate::leanh::lean_ctor_get(v_b_2667_, 1);
                crate::leanh::lean_inc_ref(v_app_2679_);
                crate::leanh::lean_dec_ref(v_b_2667_);
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
                if crate::leanh::lean_obj_tag(v___x_2683_) == 0 {
                    v_a_2684_ = crate::leanh::lean_ctor_get(v___x_2683_, 0);
                    crate::leanh::lean_inc(v_a_2684_);
                    crate::leanh::lean_dec_ref_known(v___x_2683_, 1);
                    v___x_2685_ = l_Lean_Meta_Sym_canon(
                        v_a_2684_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2685_) == 0 {
                        v_a_2686_ = crate::leanh::lean_ctor_get(v___x_2685_, 0);
                        crate::leanh::lean_inc(v_a_2686_);
                        crate::leanh::lean_dec_ref_known(v___x_2685_, 1);
                        v___x_2687_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2686_, v_a_2670_);
                        if crate::leanh::lean_obj_tag(v___x_2687_) == 0 {
                            v_a_2688_ = crate::leanh::lean_ctor_get(v___x_2687_, 0);
                            v_isSharedCheck_2697_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2687_)) as u8;
                            if v_isSharedCheck_2697_ == 0 {
                                v___x_2690_ = v___x_2687_;
                                v_isShared_2691_ = v_isSharedCheck_2697_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2688_);
                                crate::leanh::lean_dec(v___x_2687_);
                                v___x_2690_ = crate::leanh::lean_box(0);
                                v_isShared_2691_ = v_isSharedCheck_2697_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_app_2679_);
                            crate::leanh::lean_dec_ref(v_app_2677_);
                            crate::leanh::lean_dec(v_i_2668_);
                            v_a_2698_ = crate::leanh::lean_ctor_get(v___x_2687_, 0);
                            v_isSharedCheck_2705_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2687_)) as u8;
                            if v_isSharedCheck_2705_ == 0 {
                                v___x_2700_ = v___x_2687_;
                                v_isShared_2701_ = v_isSharedCheck_2705_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2698_);
                                crate::leanh::lean_dec(v___x_2687_);
                                v___x_2700_ = crate::leanh::lean_box(0);
                                v_isShared_2701_ = v_isSharedCheck_2705_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_app_2679_);
                        crate::leanh::lean_dec_ref(v_app_2677_);
                        crate::leanh::lean_dec(v_i_2668_);
                        v_a_2706_ = crate::leanh::lean_ctor_get(v___x_2685_, 0);
                        v_isSharedCheck_2713_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2685_)) as u8;
                        if v_isSharedCheck_2713_ == 0 {
                            v___x_2708_ = v___x_2685_;
                            v_isShared_2709_ = v_isSharedCheck_2713_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2706_);
                            crate::leanh::lean_dec(v___x_2685_);
                            v___x_2708_ = crate::leanh::lean_box(0);
                            v_isShared_2709_ = v_isSharedCheck_2713_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_app_2679_);
                    crate::leanh::lean_dec_ref(v_app_2677_);
                    crate::leanh::lean_dec(v_i_2668_);
                    v_a_2714_ = crate::leanh::lean_ctor_get(v___x_2683_, 0);
                    v_isSharedCheck_2721_ = (!crate::leanh::lean_is_exclusive(v___x_2683_)) as u8;
                    if v_isSharedCheck_2721_ == 0 {
                        v___x_2716_ = v___x_2683_;
                        v_isShared_2717_ = v_isSharedCheck_2721_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2714_);
                        crate::leanh::lean_dec(v___x_2683_);
                        v___x_2716_ = crate::leanh::lean_box(0);
                        v_isShared_2717_ = v_isSharedCheck_2721_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc(v_i_2668_);
                crate::leanh::lean_inc_ref(v_app_2679_);
                crate::leanh::lean_inc_ref(v_app_2677_);
                v___x_2692_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2692_, 0, v_app_2677_);
                crate::leanh::lean_ctor_set(v___x_2692_, 1, v_app_2679_);
                crate::leanh::lean_ctor_set(v___x_2692_, 2, v_i_2668_);
                v___x_2693_ = crate::leanh::lean_alloc_ctor(2, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2693_, 0, v_app_2677_);
                crate::leanh::lean_ctor_set(v___x_2693_, 1, v_app_2679_);
                crate::leanh::lean_ctor_set(v___x_2693_, 2, v_i_2668_);
                crate::leanh::lean_ctor_set(v___x_2693_, 3, v_a_2688_);
                crate::leanh::lean_ctor_set(v___x_2693_, 4, v___x_2692_);
                if v_isShared_2691_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2690_, 0, v___x_2693_);
                    v___x_2695_ = v___x_2690_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2696_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
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
                    v_reuseFailAlloc_2704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
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
                    v_reuseFailAlloc_2712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
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
                    v_reuseFailAlloc_2720_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
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
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_b_2724_: *mut crate::leanh::LeanObject,
    mut v_i_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
    mut v_a_2732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2733_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(
        v_a_2723_, v_b_2724_, v_i_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_,
        v_a_2731_,
    );
    crate::leanh::lean_dec(v_a_2731_);
    crate::leanh::lean_dec_ref(v_a_2730_);
    crate::leanh::lean_dec(v_a_2729_);
    crate::leanh::lean_dec_ref(v_a_2728_);
    crate::leanh::lean_dec(v_a_2727_);
    crate::leanh::lean_dec_ref(v_a_2726_);
    return v_res_2733_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(
    mut v_a_2734_: *mut crate::leanh::LeanObject,
    mut v_b_2735_: *mut crate::leanh::LeanObject,
    mut v_i_2736_: *mut crate::leanh::LeanObject,
    mut v_a_2737_: *mut crate::leanh::LeanObject,
    mut v_a_2738_: *mut crate::leanh::LeanObject,
    mut v_a_2739_: *mut crate::leanh::LeanObject,
    mut v_a_2740_: *mut crate::leanh::LeanObject,
    mut v_a_2741_: *mut crate::leanh::LeanObject,
    mut v_a_2742_: *mut crate::leanh::LeanObject,
    mut v_a_2743_: *mut crate::leanh::LeanObject,
    mut v_a_2744_: *mut crate::leanh::LeanObject,
    mut v_a_2745_: *mut crate::leanh::LeanObject,
    mut v_a_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(
        v_a_2734_, v_b_2735_, v_i_2736_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_,
        v_a_2746_,
    );
    return v___x_2748_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___boxed(
    mut v_a_2749_: *mut crate::leanh::LeanObject,
    mut v_b_2750_: *mut crate::leanh::LeanObject,
    mut v_i_2751_: *mut crate::leanh::LeanObject,
    mut v_a_2752_: *mut crate::leanh::LeanObject,
    mut v_a_2753_: *mut crate::leanh::LeanObject,
    mut v_a_2754_: *mut crate::leanh::LeanObject,
    mut v_a_2755_: *mut crate::leanh::LeanObject,
    mut v_a_2756_: *mut crate::leanh::LeanObject,
    mut v_a_2757_: *mut crate::leanh::LeanObject,
    mut v_a_2758_: *mut crate::leanh::LeanObject,
    mut v_a_2759_: *mut crate::leanh::LeanObject,
    mut v_a_2760_: *mut crate::leanh::LeanObject,
    mut v_a_2761_: *mut crate::leanh::LeanObject,
    mut v_a_2762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2763_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate(
        v_a_2749_, v_b_2750_, v_i_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_,
        v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_,
    );
    crate::leanh::lean_dec(v_a_2761_);
    crate::leanh::lean_dec_ref(v_a_2760_);
    crate::leanh::lean_dec(v_a_2759_);
    crate::leanh::lean_dec_ref(v_a_2758_);
    crate::leanh::lean_dec(v_a_2757_);
    crate::leanh::lean_dec_ref(v_a_2756_);
    crate::leanh::lean_dec(v_a_2755_);
    crate::leanh::lean_dec_ref(v_a_2754_);
    crate::leanh::lean_dec(v_a_2753_);
    crate::leanh::lean_dec(v_a_2752_);
    return v_res_2763_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(
    mut v_declName_2764_: *mut crate::leanh::LeanObject,
    mut v___y_2765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2767_ = lean_st_ref_get(v___y_2765_);
    v_env_2768_ = crate::leanh::lean_ctor_get(v___x_2767_, 0);
    crate::leanh::lean_inc_ref(v_env_2768_);
    crate::leanh::lean_dec(v___x_2767_);
    v___x_2769_ = l_Lean_isImplicitReducibleCore(v_env_2768_, v_declName_2764_);
    v___x_2770_ = crate::leanh::lean_box((v___x_2769_) as usize);
    v___x_2771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2771_, 0, v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg___boxed(
    mut v_declName_2772_: *mut crate::leanh::LeanObject,
    mut v___y_2773_: *mut crate::leanh::LeanObject,
    mut v___y_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2775_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_2772_, v___y_2773_);
    crate::leanh::lean_dec(v___y_2773_);
    return v_res_2775_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(
    mut v_declName_2776_: *mut crate::leanh::LeanObject,
    mut v___y_2777_: *mut crate::leanh::LeanObject,
    mut v___y_2778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2780_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_2776_, v___y_2778_);
    return v___x_2780_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___boxed(
    mut v_declName_2781_: *mut crate::leanh::LeanObject,
    mut v___y_2782_: *mut crate::leanh::LeanObject,
    mut v___y_2783_: *mut crate::leanh::LeanObject,
    mut v___y_2784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2785_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0(v_declName_2781_, v___y_2782_, v___y_2783_);
    crate::leanh::lean_dec(v___y_2783_);
    crate::leanh::lean_dec_ref(v___y_2782_);
    return v_res_2785_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(
    mut v_f_2786_: *mut crate::leanh::LeanObject,
    mut v_a_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_f_2786_) == 4 {
        let mut v_declName_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_2790_ = crate::leanh::lean_ctor_get(v_f_2786_, 0);
        crate::leanh::lean_inc(v_declName_2790_);
        crate::leanh::lean_dec_ref_known(v_f_2786_, 2);
        v___x_2791_ = l_Lean_isImplicitReducible___at___00__private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance_spec__0___redArg(v_declName_2790_, v_a_2788_);
        return v___x_2791_;
    } else {
        let mut v___x_2792_: u8 = 0;
        let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_2786_);
        v___x_2792_ = 0;
        v___x_2793_ = crate::leanh::lean_box((v___x_2792_) as usize);
        v___x_2794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2794_, 0, v___x_2793_);
        return v___x_2794_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance___boxed(
    mut v_f_2795_: *mut crate::leanh::LeanObject,
    mut v_a_2796_: *mut crate::leanh::LeanObject,
    mut v_a_2797_: *mut crate::leanh::LeanObject,
    mut v_a_2798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2799_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(
        v_f_2795_, v_a_2796_, v_a_2797_,
    );
    crate::leanh::lean_dec(v_a_2797_);
    crate::leanh::lean_dec_ref(v_a_2796_);
    return v_res_2799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(
    mut v_as_2800_: *mut crate::leanh::LeanObject,
    mut v_sz_2801_: usize,
    mut v_i_2802_: usize,
    mut v_b_2803_: *mut crate::leanh::LeanObject,
    mut v___y_2804_: *mut crate::leanh::LeanObject,
    mut v___y_2805_: *mut crate::leanh::LeanObject,
    mut v___y_2806_: *mut crate::leanh::LeanObject,
    mut v___y_2807_: *mut crate::leanh::LeanObject,
    mut v___y_2808_: *mut crate::leanh::LeanObject,
    mut v___y_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
    mut v___y_2811_: *mut crate::leanh::LeanObject,
    mut v___y_2812_: *mut crate::leanh::LeanObject,
    mut v___y_2813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: usize = 0;
    let mut v___x_2821_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2815_ = lean_usize_dec_lt(v_i_2802_, v_sz_2801_);
                if v___x_2815_ == 0 {
                    v___x_2816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2816_, 0, v_b_2803_);
                    return v___x_2816_;
                } else {
                    v_a_2817_ = lean_array_uget_borrowed(v_as_2800_, v_i_2802_);
                    crate::leanh::lean_inc(v_a_2817_);
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
                    if crate::leanh::lean_obj_tag(v___x_2818_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2818_, 1);
                        v___x_2819_ = crate::leanh::lean_box(0);
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
    mut v_as_2823_: *mut crate::leanh::LeanObject,
    mut v_sz_2824_: *mut crate::leanh::LeanObject,
    mut v_i_2825_: *mut crate::leanh::LeanObject,
    mut v_b_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
    mut v___y_2828_: *mut crate::leanh::LeanObject,
    mut v___y_2829_: *mut crate::leanh::LeanObject,
    mut v___y_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2838_: usize = 0;
    let mut v_i_boxed_2839_: usize = 0;
    let mut v_res_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2838_ = crate::leanh::lean_unbox_usize(v_sz_2824_);
    crate::leanh::lean_dec(v_sz_2824_);
    v_i_boxed_2839_ = crate::leanh::lean_unbox_usize(v_i_2825_);
    crate::leanh::lean_dec(v_i_2825_);
    v_res_2840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_as_2823_, v_sz_boxed_2838_, v_i_boxed_2839_, v_b_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
    crate::leanh::lean_dec(v___y_2836_);
    crate::leanh::lean_dec_ref(v___y_2835_);
    crate::leanh::lean_dec(v___y_2834_);
    crate::leanh::lean_dec_ref(v___y_2833_);
    crate::leanh::lean_dec(v___y_2832_);
    crate::leanh::lean_dec_ref(v___y_2831_);
    crate::leanh::lean_dec(v___y_2830_);
    crate::leanh::lean_dec_ref(v___y_2829_);
    crate::leanh::lean_dec(v___y_2828_);
    crate::leanh::lean_dec(v___y_2827_);
    crate::leanh::lean_dec_ref(v_as_2823_);
    return v_res_2840_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_mbtc_spec__11(
    mut v_x_2841_: *mut crate::leanh::LeanObject,
    mut v_x_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2842_) == 0 {
                    return v_x_2841_;
                } else {
                    v_key_2843_ = crate::leanh::lean_ctor_get(v_x_2842_, 0);
                    crate::leanh::lean_inc(v_key_2843_);
                    v_tail_2844_ = crate::leanh::lean_ctor_get(v_x_2842_, 2);
                    crate::leanh::lean_inc(v_tail_2844_);
                    crate::leanh::lean_dec_ref_known(v_x_2842_, 3);
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
    mut v_as_2847_: *mut crate::leanh::LeanObject,
    mut v_i_2848_: usize,
    mut v_stop_2849_: usize,
    mut v_b_2850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: usize = 0;
    let mut v___x_2855_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2851_ = lean_usize_dec_eq(v_i_2848_, v_stop_2849_);
                if v___x_2851_ == 0 {
                    v___x_2852_ = lean_array_uget_borrowed(v_as_2847_, v_i_2848_);
                    crate::leanh::lean_inc(v___x_2852_);
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
    mut v_as_2857_: *mut crate::leanh::LeanObject,
    mut v_i_2858_: *mut crate::leanh::LeanObject,
    mut v_stop_2859_: *mut crate::leanh::LeanObject,
    mut v_b_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2861_: usize = 0;
    let mut v_stop_boxed_2862_: usize = 0;
    let mut v_res_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2861_ = crate::leanh::lean_unbox_usize(v_i_2858_);
    crate::leanh::lean_dec(v_i_2858_);
    v_stop_boxed_2862_ = crate::leanh::lean_unbox_usize(v_stop_2859_);
    crate::leanh::lean_dec(v_stop_2859_);
    v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_as_2857_, v_i_boxed_2861_, v_stop_boxed_2862_, v_b_2860_);
    crate::leanh::lean_dec_ref(v_as_2857_);
    return v_res_2863_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(
    mut v_hi_2864_: *mut crate::leanh::LeanObject,
    mut v_pivot_2865_: *mut crate::leanh::LeanObject,
    mut v_as_2866_: *mut crate::leanh::LeanObject,
    mut v_i_2867_: *mut crate::leanh::LeanObject,
    mut v_k_2868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2869_: u8 = 0;
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2869_ = lean_nat_dec_lt(v_k_2868_, v_hi_2864_);
                if v___x_2869_ == 0 {
                    crate::leanh::lean_dec(v_k_2868_);
                    v___x_2870_ = lean_array_fswap(v_as_2866_, v_i_2867_, v_hi_2864_);
                    v___x_2871_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2871_, 0, v_i_2867_);
                    crate::leanh::lean_ctor_set(v___x_2871_, 1, v___x_2870_);
                    return v___x_2871_;
                } else {
                    v___x_2872_ = lean_array_fget_borrowed(v_as_2866_, v_k_2868_);
                    v___x_2873_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2872_, v_pivot_2865_);
                    if v___x_2873_ == 0 {
                        v___x_2874_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2875_ = lean_nat_add(v_k_2868_, v___x_2874_);
                        crate::leanh::lean_dec(v_k_2868_);
                        v_k_2868_ = v___x_2875_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2877_ = lean_array_fswap(v_as_2866_, v_i_2867_, v_k_2868_);
                        v___x_2878_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2879_ = lean_nat_add(v_i_2867_, v___x_2878_);
                        crate::leanh::lean_dec(v_i_2867_);
                        v___x_2880_ = lean_nat_add(v_k_2868_, v___x_2878_);
                        crate::leanh::lean_dec(v_k_2868_);
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
    mut v_hi_2882_: *mut crate::leanh::LeanObject,
    mut v_pivot_2883_: *mut crate::leanh::LeanObject,
    mut v_as_2884_: *mut crate::leanh::LeanObject,
    mut v_i_2885_: *mut crate::leanh::LeanObject,
    mut v_k_2886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2887_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2882_, v_pivot_2883_, v_as_2884_, v_i_2885_, v_k_2886_);
    crate::leanh::lean_dec_ref(v_pivot_2883_);
    crate::leanh::lean_dec(v_hi_2882_);
    return v_res_2887_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(
    mut v_n_2888_: *mut crate::leanh::LeanObject,
    mut v_as_2889_: *mut crate::leanh::LeanObject,
    mut v_lo_2890_: *mut crate::leanh::LeanObject,
    mut v_hi_2891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: u8 = 0;
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2903_ = lean_nat_dec_lt(v_lo_2890_, v_hi_2891_);
                if v___x_2903_ == 0 {
                    crate::leanh::lean_dec(v_lo_2890_);
                    return v_as_2889_;
                } else {
                    v___x_2904_ = lean_nat_add(v_lo_2890_, v_hi_2891_);
                    v___x_2905_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_2906_ = lean_nat_shiftr(v___x_2904_, v___x_2905_);
                    crate::leanh::lean_dec(v___x_2904_);
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
                crate::leanh::lean_inc_n(v_lo_2890_, 2);
                v___x_2895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_2891_, v_pivot_2894_, v___y_2893_, v_lo_2890_, v_lo_2890_);
                crate::leanh::lean_dec(v_pivot_2894_);
                v_fst_2896_ = crate::leanh::lean_ctor_get(v___x_2895_, 0);
                crate::leanh::lean_inc(v_fst_2896_);
                v_snd_2897_ = crate::leanh::lean_ctor_get(v___x_2895_, 1);
                crate::leanh::lean_inc(v_snd_2897_);
                crate::leanh::lean_dec_ref(v___x_2895_);
                v___x_2898_ = lean_nat_dec_le(v_hi_2891_, v_fst_2896_);
                if v___x_2898_ == 0 {
                    v___x_2899_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2888_, v_snd_2897_, v_lo_2890_, v_fst_2896_);
                    v___x_2900_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2901_ = lean_nat_add(v_fst_2896_, v___x_2900_);
                    crate::leanh::lean_dec(v_fst_2896_);
                    v_as_2889_ = v___x_2899_;
                    v_lo_2890_ = v___x_2901_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_2896_);
                    crate::leanh::lean_dec(v_lo_2890_);
                    return v_snd_2897_;
                }
            }
            2 => {
                v___x_2909_ = lean_array_fget_borrowed(v___y_2908_, v_mid_2906_);
                v___x_2910_ = lean_array_fget_borrowed(v___y_2908_, v_hi_2891_);
                v___x_2911_ = l_Lean_Meta_Grind_SplitInfo_lt(v___x_2909_, v___x_2910_);
                if v___x_2911_ == 0 {
                    crate::leanh::lean_dec(v_mid_2906_);
                    v___y_2893_ = v___y_2908_;
                    state = 1;
                    continue;
                } else {
                    v___x_2912_ = lean_array_fswap(v___y_2908_, v_mid_2906_, v_hi_2891_);
                    crate::leanh::lean_dec(v_mid_2906_);
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
    mut v_n_2923_: *mut crate::leanh::LeanObject,
    mut v_as_2924_: *mut crate::leanh::LeanObject,
    mut v_lo_2925_: *mut crate::leanh::LeanObject,
    mut v_hi_2926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2927_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_2923_, v_as_2924_, v_lo_2925_, v_hi_2926_);
    crate::leanh::lean_dec(v_hi_2926_);
    crate::leanh::lean_dec(v_n_2923_);
    return v_res_2927_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(
    mut v_a_2928_: *mut crate::leanh::LeanObject,
    mut v_x_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: u8 = 0;
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2929_) == 0 {
                    v___x_2930_ = crate::leanh::lean_box(0);
                    return v___x_2930_;
                } else {
                    v_key_2931_ = crate::leanh::lean_ctor_get(v_x_2929_, 0);
                    v_value_2932_ = crate::leanh::lean_ctor_get(v_x_2929_, 1);
                    v_tail_2933_ = crate::leanh::lean_ctor_get(v_x_2929_, 2);
                    v___x_2934_ = lean_expr_eqv(v_key_2931_, v_a_2928_);
                    if v___x_2934_ == 0 {
                        v_x_2929_ = v_tail_2933_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2932_);
                        v___x_2936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2936_, 0, v_value_2932_);
                        return v___x_2936_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg___boxed(
    mut v_a_2937_: *mut crate::leanh::LeanObject,
    mut v_x_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2939_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_2937_, v_x_2938_);
    crate::leanh::lean_dec(v_x_2938_);
    crate::leanh::lean_dec_ref(v_a_2937_);
    return v_res_2939_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(
    mut v_m_2940_: *mut crate::leanh::LeanObject,
    mut v_a_2941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2942_ = crate::leanh::lean_ctor_get(v_m_2940_, 1);
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
    mut v_m_2958_: *mut crate::leanh::LeanObject,
    mut v_a_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_2958_, v_a_2959_);
    crate::leanh::lean_dec_ref(v_a_2959_);
    crate::leanh::lean_dec_ref(v_m_2958_);
    return v_res_2960_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(
    mut v_msgData_2961_: *mut crate::leanh::LeanObject,
    mut v___y_2962_: *mut crate::leanh::LeanObject,
    mut v___y_2963_: *mut crate::leanh::LeanObject,
    mut v___y_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2967_ = lean_st_ref_get(v___y_2965_);
    v_env_2968_ = crate::leanh::lean_ctor_get(v___x_2967_, 0);
    crate::leanh::lean_inc_ref(v_env_2968_);
    crate::leanh::lean_dec(v___x_2967_);
    v___x_2969_ = lean_st_ref_get(v___y_2963_);
    v_mctx_2970_ = crate::leanh::lean_ctor_get(v___x_2969_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2970_);
    crate::leanh::lean_dec(v___x_2969_);
    v_lctx_2971_ = crate::leanh::lean_ctor_get(v___y_2962_, 2);
    v_options_2972_ = crate::leanh::lean_ctor_get(v___y_2964_, 2);
    crate::leanh::lean_inc_ref(v_options_2972_);
    crate::leanh::lean_inc_ref(v_lctx_2971_);
    v___x_2973_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2973_, 0, v_env_2968_);
    crate::leanh::lean_ctor_set(v___x_2973_, 1, v_mctx_2970_);
    crate::leanh::lean_ctor_set(v___x_2973_, 2, v_lctx_2971_);
    crate::leanh::lean_ctor_set(v___x_2973_, 3, v_options_2972_);
    v___x_2974_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2974_, 0, v___x_2973_);
    crate::leanh::lean_ctor_set(v___x_2974_, 1, v_msgData_2961_);
    v___x_2975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2975_, 0, v___x_2974_);
    return v___x_2975_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0___boxed(
    mut v_msgData_2976_: *mut crate::leanh::LeanObject,
    mut v___y_2977_: *mut crate::leanh::LeanObject,
    mut v___y_2978_: *mut crate::leanh::LeanObject,
    mut v___y_2979_: *mut crate::leanh::LeanObject,
    mut v___y_2980_: *mut crate::leanh::LeanObject,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msgData_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
    crate::leanh::lean_dec(v___y_2980_);
    crate::leanh::lean_dec_ref(v___y_2979_);
    crate::leanh::lean_dec(v___y_2978_);
    crate::leanh::lean_dec_ref(v___y_2977_);
    return v_res_2982_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: f64 = 0.0;
    v___x_2983_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2984_ = lean_float_of_nat(v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(
    mut v_cls_2988_: *mut crate::leanh::LeanObject,
    mut v_msg_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v_tid_3014_: u64 = 0;
    let mut v_traces_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: f64 = 0.0;
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v_isSharedCheck_3040_: u8 = 0;
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2995_ = crate::leanh::lean_ctor_get(v___y_2992_, 5);
                v___x_2996_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0_spec__0(v_msg_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
                v_a_2997_ = crate::leanh::lean_ctor_get(v___x_2996_, 0);
                v_isSharedCheck_3041_ = (!crate::leanh::lean_is_exclusive(v___x_2996_)) as u8;
                if v_isSharedCheck_3041_ == 0 {
                    v___x_2999_ = v___x_2996_;
                    v_isShared_3000_ = v_isSharedCheck_3041_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2997_);
                    crate::leanh::lean_dec(v___x_2996_);
                    v___x_2999_ = crate::leanh::lean_box(0);
                    v_isShared_3000_ = v_isSharedCheck_3041_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3001_ = lean_st_ref_take(v___y_2993_);
                v_traceState_3002_ = crate::leanh::lean_ctor_get(v___x_3001_, 4);
                v_env_3003_ = crate::leanh::lean_ctor_get(v___x_3001_, 0);
                v_nextMacroScope_3004_ = crate::leanh::lean_ctor_get(v___x_3001_, 1);
                v_ngen_3005_ = crate::leanh::lean_ctor_get(v___x_3001_, 2);
                v_auxDeclNGen_3006_ = crate::leanh::lean_ctor_get(v___x_3001_, 3);
                v_cache_3007_ = crate::leanh::lean_ctor_get(v___x_3001_, 5);
                v_messages_3008_ = crate::leanh::lean_ctor_get(v___x_3001_, 6);
                v_infoState_3009_ = crate::leanh::lean_ctor_get(v___x_3001_, 7);
                v_snapshotTasks_3010_ = crate::leanh::lean_ctor_get(v___x_3001_, 8);
                v_isSharedCheck_3040_ = (!crate::leanh::lean_is_exclusive(v___x_3001_)) as u8;
                if v_isSharedCheck_3040_ == 0 {
                    v___x_3012_ = v___x_3001_;
                    v_isShared_3013_ = v_isSharedCheck_3040_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3010_);
                    crate::leanh::lean_inc(v_infoState_3009_);
                    crate::leanh::lean_inc(v_messages_3008_);
                    crate::leanh::lean_inc(v_cache_3007_);
                    crate::leanh::lean_inc(v_traceState_3002_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3006_);
                    crate::leanh::lean_inc(v_ngen_3005_);
                    crate::leanh::lean_inc(v_nextMacroScope_3004_);
                    crate::leanh::lean_inc(v_env_3003_);
                    crate::leanh::lean_dec(v___x_3001_);
                    v___x_3012_ = crate::leanh::lean_box(0);
                    v_isShared_3013_ = v_isSharedCheck_3040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3014_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3002_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3015_ = crate::leanh::lean_ctor_get(v_traceState_3002_, 0);
                v_isSharedCheck_3039_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3002_)) as u8;
                if v_isSharedCheck_3039_ == 0 {
                    v___x_3017_ = v_traceState_3002_;
                    v_isShared_3018_ = v_isSharedCheck_3039_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3015_);
                    crate::leanh::lean_dec(v_traceState_3002_);
                    v___x_3017_ = crate::leanh::lean_box(0);
                    v_isShared_3018_ = v_isSharedCheck_3039_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3019_ = crate::leanh::lean_box(0);
                v___x_3020_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__0);
                v___x_3021_ = 0;
                v___x_3022_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__1;
                v___x_3023_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3023_, 0, v_cls_2988_);
                crate::leanh::lean_ctor_set(v___x_3023_, 1, v___x_3019_);
                crate::leanh::lean_ctor_set(v___x_3023_, 2, v___x_3022_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3020_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3020_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3021_,
                );
                v___x_3024_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg___closed__2;
                v___x_3025_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3025_, 0, v___x_3023_);
                crate::leanh::lean_ctor_set(v___x_3025_, 1, v_a_2997_);
                crate::leanh::lean_ctor_set(v___x_3025_, 2, v___x_3024_);
                crate::leanh::lean_inc(v_ref_2995_);
                v___x_3026_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3026_, 0, v_ref_2995_);
                crate::leanh::lean_ctor_set(v___x_3026_, 1, v___x_3025_);
                v___x_3027_ = l_Lean_PersistentArray_push___redArg(v_traces_3015_, v___x_3026_);
                if v_isShared_3018_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3017_, 0, v___x_3027_);
                    v___x_3029_ = v___x_3017_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3027_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3038_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3014_,
                    );
                    v___x_3029_ = v_reuseFailAlloc_3038_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3013_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3012_, 4, v___x_3029_);
                    v___x_3031_ = v___x_3012_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_env_3003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_nextMacroScope_3004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_ngen_3005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 3, v_auxDeclNGen_3006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 4, v___x_3029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 5, v_cache_3007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 6, v_messages_3008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 7, v_infoState_3009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 8, v_snapshotTasks_3010_);
                    v___x_3031_ = v_reuseFailAlloc_3037_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3032_ = lean_st_ref_set(v___y_2993_, v___x_3031_);
                v___x_3033_ = crate::leanh::lean_box(0);
                if v_isShared_3000_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2999_, 0, v___x_3033_);
                    v___x_3035_ = v___x_2999_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
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
    mut v_cls_3042_: *mut crate::leanh::LeanObject,
    mut v_msg_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
    mut v___y_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
    mut v___y_3047_: *mut crate::leanh::LeanObject,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3049_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(
        v_cls_3042_,
        v_msg_3043_,
        v___y_3044_,
        v___y_3045_,
        v___y_3046_,
        v___y_3047_,
    );
    crate::leanh::lean_dec(v___y_3047_);
    crate::leanh::lean_dec_ref(v___y_3046_);
    crate::leanh::lean_dec(v___y_3045_);
    crate::leanh::lean_dec_ref(v___y_3044_);
    return v_res_3049_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(
    mut v_a_3050_: *mut crate::leanh::LeanObject,
    mut v_x_3051_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3052_: u8 = 0;
    let mut v_key_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3051_) == 0 {
                    v___x_3052_ = 0;
                    return v___x_3052_;
                } else {
                    v_key_3053_ = crate::leanh::lean_ctor_get(v_x_3051_, 0);
                    v_tail_3054_ = crate::leanh::lean_ctor_get(v_x_3051_, 2);
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
    mut v_a_3057_: *mut crate::leanh::LeanObject,
    mut v_x_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3059_: u8 = 0;
    let mut v_r_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_3057_, v_x_3058_);
    crate::leanh::lean_dec(v_x_3058_);
    crate::leanh::lean_dec_ref(v_a_3057_);
    v_r_3060_ = crate::leanh::lean_box((v_res_3059_) as usize);
    return v_r_3060_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(
    mut v_x_3061_: *mut crate::leanh::LeanObject,
    mut v_x_3062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3068_: u8 = 0;
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3062_) == 0 {
                    return v_x_3061_;
                } else {
                    v_key_3063_ = crate::leanh::lean_ctor_get(v_x_3062_, 0);
                    v_value_3064_ = crate::leanh::lean_ctor_get(v_x_3062_, 1);
                    v_tail_3065_ = crate::leanh::lean_ctor_get(v_x_3062_, 2);
                    v_isSharedCheck_3088_ = (!crate::leanh::lean_is_exclusive(v_x_3062_)) as u8;
                    if v_isSharedCheck_3088_ == 0 {
                        v___x_3067_ = v_x_3062_;
                        v_isShared_3068_ = v_isSharedCheck_3088_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3065_);
                        crate::leanh::lean_inc(v_value_3064_);
                        crate::leanh::lean_inc(v_key_3063_);
                        crate::leanh::lean_dec(v_x_3062_);
                        v___x_3067_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v___x_3082_);
                if v_isShared_3068_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3067_, 2, v___x_3082_);
                    v___x_3084_ = v___x_3067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3087_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_key_3063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_value_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3087_, 2, v___x_3082_);
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
    mut v_i_3089_: *mut crate::leanh::LeanObject,
    mut v_source_3090_: *mut crate::leanh::LeanObject,
    mut v_target_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v_es_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3092_ = lean_array_get_size(v_source_3090_);
                v___x_3093_ = lean_nat_dec_lt(v_i_3089_, v___x_3092_);
                if v___x_3093_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3090_);
                    crate::leanh::lean_dec(v_i_3089_);
                    return v_target_3091_;
                } else {
                    v_es_3094_ = lean_array_fget(v_source_3090_, v_i_3089_);
                    v___x_3095_ = crate::leanh::lean_box(0);
                    v_source_3096_ = lean_array_fset(v_source_3090_, v_i_3089_, v___x_3095_);
                    v_target_3097_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_target_3091_, v_es_3094_);
                    v___x_3098_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3099_ = lean_nat_add(v_i_3089_, v___x_3098_);
                    crate::leanh::lean_dec(v_i_3089_);
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
    mut v_data_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = lean_array_get_size(v_data_3101_);
    v___x_3103_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3104_ = lean_nat_mul(v___x_3102_, v___x_3103_);
    v___x_3105_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3106_ = crate::leanh::lean_box(0);
    v___x_3107_ = lean_mk_array(v_nbuckets_3104_, v___x_3106_);
    v___x_3108_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v___x_3105_, v_data_3101_, v___x_3107_);
    return v___x_3108_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(
    mut v_m_3109_: *mut crate::leanh::LeanObject,
    mut v_a_3110_: *mut crate::leanh::LeanObject,
    mut v_b_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v_val_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3149_: u8 = 0;
    let mut v_unused_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3112_ = crate::leanh::lean_ctor_get(v_m_3109_, 0);
                v_buckets_3113_ = crate::leanh::lean_ctor_get(v_m_3109_, 1);
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
                    crate::leanh::lean_inc_ref(v_buckets_3113_);
                    crate::leanh::lean_inc(v_size_3112_);
                    v_isSharedCheck_3149_ = (!crate::leanh::lean_is_exclusive(v_m_3109_)) as u8;
                    if v_isSharedCheck_3149_ == 0 {
                        v_unused_3150_ = crate::leanh::lean_ctor_get(v_m_3109_, 1);
                        crate::leanh::lean_dec(v_unused_3150_);
                        v_unused_3151_ = crate::leanh::lean_ctor_get(v_m_3109_, 0);
                        crate::leanh::lean_dec(v_unused_3151_);
                        v___x_3130_ = v_m_3109_;
                        v_isShared_3131_ = v_isSharedCheck_3149_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3109_);
                        v___x_3130_ = crate::leanh::lean_box(0);
                        v_isShared_3131_ = v_isSharedCheck_3149_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3111_);
                    crate::leanh::lean_dec_ref(v_a_3110_);
                    return v_m_3109_;
                }
            }
            1 => {
                v___x_3132_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3133_ = lean_nat_add(v_size_3112_, v___x_3132_);
                crate::leanh::lean_dec(v_size_3112_);
                crate::leanh::lean_inc(v_bkt_3127_);
                v___x_3134_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3134_, 0, v_a_3110_);
                crate::leanh::lean_ctor_set(v___x_3134_, 1, v_b_3111_);
                crate::leanh::lean_ctor_set(v___x_3134_, 2, v_bkt_3127_);
                v_buckets_x27_3135_ = lean_array_uset(v_buckets_3113_, v___x_3126_, v___x_3134_);
                v___x_3136_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3137_ = lean_nat_mul(v_size_x27_3133_, v___x_3136_);
                v___x_3138_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3139_ = lean_nat_div(v___x_3137_, v___x_3138_);
                crate::leanh::lean_dec(v___x_3137_);
                v___x_3140_ = lean_array_get_size(v_buckets_x27_3135_);
                v___x_3141_ = lean_nat_dec_le(v___x_3139_, v___x_3140_);
                crate::leanh::lean_dec(v___x_3139_);
                if v___x_3141_ == 0 {
                    v_val_3142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_buckets_x27_3135_);
                    if v_isShared_3131_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3130_, 1, v_val_3142_);
                        crate::leanh::lean_ctor_set(v___x_3130_, 0, v_size_x27_3133_);
                        v___x_3144_ = v___x_3130_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3145_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_size_x27_3133_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_val_3142_);
                        v___x_3144_ = v_reuseFailAlloc_3145_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_3131_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3130_, 1, v_buckets_x27_3135_);
                        crate::leanh::lean_ctor_set(v___x_3130_, 0, v_size_x27_3133_);
                        v___x_3147_ = v___x_3130_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_size_x27_3133_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_buckets_x27_3135_);
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
    mut v_ctx_3152_: *mut crate::leanh::LeanObject,
    mut v_val_3153_: *mut crate::leanh::LeanObject,
    mut v___x_3154_: *mut crate::leanh::LeanObject,
    mut v___x_3155_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3156_: *mut crate::leanh::LeanObject,
    mut v_b_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqAssignment_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: u8 = 0;
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v_a_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_a_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3156_) == 0 {
                    crate::leanh::lean_dec(v___x_3155_);
                    crate::leanh::lean_dec_ref(v___x_3154_);
                    crate::leanh::lean_dec_ref(v_val_3153_);
                    crate::leanh::lean_dec_ref(v_ctx_3152_);
                    v___x_3169_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3169_, 0, v_b_3157_);
                    return v___x_3169_;
                } else {
                    v_head_3170_ = crate::leanh::lean_ctor_get(v_as_x27_3156_, 0);
                    v_tail_3171_ = crate::leanh::lean_ctor_get(v_as_x27_3156_, 1);
                    v_eqAssignment_3172_ = crate::leanh::lean_ctor_get(v_ctx_3152_, 2);
                    v_arg_3173_ = crate::leanh::lean_ctor_get(v_head_3170_, 0);
                    crate::leanh::lean_inc_ref(v_eqAssignment_3172_);
                    crate::leanh::lean_inc(v___y_3167_);
                    crate::leanh::lean_inc_ref(v___y_3166_);
                    crate::leanh::lean_inc(v___y_3165_);
                    crate::leanh::lean_inc_ref(v___y_3164_);
                    crate::leanh::lean_inc(v___y_3163_);
                    crate::leanh::lean_inc_ref(v___y_3162_);
                    crate::leanh::lean_inc(v___y_3161_);
                    crate::leanh::lean_inc_ref(v___y_3160_);
                    crate::leanh::lean_inc(v___y_3159_);
                    crate::leanh::lean_inc(v___y_3158_);
                    crate::leanh::lean_inc_ref(v_arg_3173_);
                    crate::leanh::lean_inc_ref(v_val_3153_);
                    v___x_3174_ = crate::leanh::lean_apply_13(
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
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3174_) == 0 {
                        v_a_3175_ = crate::leanh::lean_ctor_get(v___x_3174_, 0);
                        crate::leanh::lean_inc(v_a_3175_);
                        crate::leanh::lean_dec_ref_known(v___x_3174_, 1);
                        v___x_3176_ = (crate::leanh::lean_unbox(v_a_3175_) as u8);
                        crate::leanh::lean_dec(v_a_3175_);
                        if v___x_3176_ == 0 {
                            v_as_x27_3156_ = v_tail_3171_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_arg_3173_);
                            crate::leanh::lean_inc_ref(v_val_3153_);
                            v___x_3178_ = l_Lean_Meta_Grind_hasSameType(
                                v_val_3153_,
                                v_arg_3173_,
                                v___y_3164_,
                                v___y_3165_,
                                v___y_3166_,
                                v___y_3167_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3178_) == 0 {
                                v_a_3179_ = crate::leanh::lean_ctor_get(v___x_3178_, 0);
                                crate::leanh::lean_inc(v_a_3179_);
                                crate::leanh::lean_dec_ref_known(v___x_3178_, 1);
                                v___x_3180_ = (crate::leanh::lean_unbox(v_a_3179_) as u8);
                                crate::leanh::lean_dec(v_a_3179_);
                                if v___x_3180_ == 0 {
                                    v_as_x27_3156_ = v_tail_3171_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v___x_3155_);
                                    crate::leanh::lean_inc(v_head_3170_);
                                    crate::leanh::lean_inc_ref(v___x_3154_);
                                    v___x_3182_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkCandidate___redArg(v___x_3154_, v_head_3170_, v___x_3155_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
                                    if crate::leanh::lean_obj_tag(v___x_3182_) == 0 {
                                        v_a_3183_ = crate::leanh::lean_ctor_get(v___x_3182_, 0);
                                        crate::leanh::lean_inc(v_a_3183_);
                                        crate::leanh::lean_dec_ref_known(v___x_3182_, 1);
                                        v___x_3184_ = crate::leanh::lean_box(0);
                                        v___x_3185_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_b_3157_, v_a_3183_, v___x_3184_);
                                        v_as_x27_3156_ = v_tail_3171_;
                                        v_b_3157_ = v___x_3185_;
                                        state = 0;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_3157_);
                                        crate::leanh::lean_dec(v___x_3155_);
                                        crate::leanh::lean_dec_ref(v___x_3154_);
                                        crate::leanh::lean_dec_ref(v_val_3153_);
                                        crate::leanh::lean_dec_ref(v_ctx_3152_);
                                        v_a_3187_ = crate::leanh::lean_ctor_get(v___x_3182_, 0);
                                        v_isSharedCheck_3194_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3182_)) as u8;
                                        if v_isSharedCheck_3194_ == 0 {
                                            v___x_3189_ = v___x_3182_;
                                            v_isShared_3190_ = v_isSharedCheck_3194_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3187_);
                                            crate::leanh::lean_dec(v___x_3182_);
                                            v___x_3189_ = crate::leanh::lean_box(0);
                                            v_isShared_3190_ = v_isSharedCheck_3194_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_b_3157_);
                                crate::leanh::lean_dec(v___x_3155_);
                                crate::leanh::lean_dec_ref(v___x_3154_);
                                crate::leanh::lean_dec_ref(v_val_3153_);
                                crate::leanh::lean_dec_ref(v_ctx_3152_);
                                v_a_3195_ = crate::leanh::lean_ctor_get(v___x_3178_, 0);
                                v_isSharedCheck_3202_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3178_)) as u8;
                                if v_isSharedCheck_3202_ == 0 {
                                    v___x_3197_ = v___x_3178_;
                                    v_isShared_3198_ = v_isSharedCheck_3202_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3195_);
                                    crate::leanh::lean_dec(v___x_3178_);
                                    v___x_3197_ = crate::leanh::lean_box(0);
                                    v_isShared_3198_ = v_isSharedCheck_3202_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3157_);
                        crate::leanh::lean_dec(v___x_3155_);
                        crate::leanh::lean_dec_ref(v___x_3154_);
                        crate::leanh::lean_dec_ref(v_val_3153_);
                        crate::leanh::lean_dec_ref(v_ctx_3152_);
                        v_a_3203_ = crate::leanh::lean_ctor_get(v___x_3174_, 0);
                        v_isSharedCheck_3210_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3174_)) as u8;
                        if v_isSharedCheck_3210_ == 0 {
                            v___x_3205_ = v___x_3174_;
                            v_isShared_3206_ = v_isSharedCheck_3210_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3203_);
                            crate::leanh::lean_dec(v___x_3174_);
                            v___x_3205_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
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
                    v_reuseFailAlloc_3201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
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
                    v_reuseFailAlloc_3209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctx_3211_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_val_3212_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_3213_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3214_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_as_x27_3215_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_3216_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_3217_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_3218_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_3219_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_3220_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3221_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3222_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3223_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3224_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3225_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3226_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3227_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_3226_);
    crate::leanh::lean_dec_ref(v___y_3225_);
    crate::leanh::lean_dec(v___y_3224_);
    crate::leanh::lean_dec_ref(v___y_3223_);
    crate::leanh::lean_dec(v___y_3222_);
    crate::leanh::lean_dec_ref(v___y_3221_);
    crate::leanh::lean_dec(v___y_3220_);
    crate::leanh::lean_dec_ref(v___y_3219_);
    crate::leanh::lean_dec(v___y_3218_);
    crate::leanh::lean_dec(v___y_3217_);
    crate::leanh::lean_dec(v_as_x27_3215_);
    return v_res_3228_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(
    mut v_a_3229_: *mut crate::leanh::LeanObject,
    mut v_b_3230_: *mut crate::leanh::LeanObject,
    mut v_x_3231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3238_: u8 = 0;
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3231_) == 0 {
                    crate::leanh::lean_dec(v_b_3230_);
                    crate::leanh::lean_dec_ref(v_a_3229_);
                    return v_x_3231_;
                } else {
                    v_key_3232_ = crate::leanh::lean_ctor_get(v_x_3231_, 0);
                    v_value_3233_ = crate::leanh::lean_ctor_get(v_x_3231_, 1);
                    v_tail_3234_ = crate::leanh::lean_ctor_get(v_x_3231_, 2);
                    v_isSharedCheck_3246_ = (!crate::leanh::lean_is_exclusive(v_x_3231_)) as u8;
                    if v_isSharedCheck_3246_ == 0 {
                        v___x_3236_ = v_x_3231_;
                        v_isShared_3237_ = v_isSharedCheck_3246_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3234_);
                        crate::leanh::lean_inc(v_value_3233_);
                        crate::leanh::lean_inc(v_key_3232_);
                        crate::leanh::lean_dec(v_x_3231_);
                        v___x_3236_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_3236_, 2, v___x_3239_);
                        v___x_3241_ = v___x_3236_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3242_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_key_3232_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_value_3233_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 2, v___x_3239_);
                        v___x_3241_ = v_reuseFailAlloc_3242_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3233_);
                    crate::leanh::lean_dec(v_key_3232_);
                    if v_isShared_3237_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3236_, 1, v_b_3230_);
                        crate::leanh::lean_ctor_set(v___x_3236_, 0, v_a_3229_);
                        v___x_3244_ = v___x_3236_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3245_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3229_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_b_3230_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 2, v_tail_3234_);
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
    mut v_a_3247_: *mut crate::leanh::LeanObject,
    mut v_x_3248_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3249_: u8 = 0;
    let mut v_key_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3248_) == 0 {
                    v___x_3249_ = 0;
                    return v___x_3249_;
                } else {
                    v_key_3250_ = crate::leanh::lean_ctor_get(v_x_3248_, 0);
                    v_tail_3251_ = crate::leanh::lean_ctor_get(v_x_3248_, 2);
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
    mut v_a_3254_: *mut crate::leanh::LeanObject,
    mut v_x_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3256_: u8 = 0;
    let mut v_r_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3256_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_3254_, v_x_3255_);
    crate::leanh::lean_dec(v_x_3255_);
    crate::leanh::lean_dec_ref(v_a_3254_);
    v_r_3257_ = crate::leanh::lean_box((v_res_3256_) as usize);
    return v_r_3257_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(
    mut v_x_3258_: *mut crate::leanh::LeanObject,
    mut v_x_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3259_) == 0 {
                    return v_x_3258_;
                } else {
                    v_key_3260_ = crate::leanh::lean_ctor_get(v_x_3259_, 0);
                    v_value_3261_ = crate::leanh::lean_ctor_get(v_x_3259_, 1);
                    v_tail_3262_ = crate::leanh::lean_ctor_get(v_x_3259_, 2);
                    v_isSharedCheck_3285_ = (!crate::leanh::lean_is_exclusive(v_x_3259_)) as u8;
                    if v_isSharedCheck_3285_ == 0 {
                        v___x_3264_ = v_x_3259_;
                        v_isShared_3265_ = v_isSharedCheck_3285_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3262_);
                        crate::leanh::lean_inc(v_value_3261_);
                        crate::leanh::lean_inc(v_key_3260_);
                        crate::leanh::lean_dec(v_x_3259_);
                        v___x_3264_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v___x_3279_);
                if v_isShared_3265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3264_, 2, v___x_3279_);
                    v___x_3281_ = v___x_3264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_key_3260_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_value_3261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 2, v___x_3279_);
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
    mut v_i_3286_: *mut crate::leanh::LeanObject,
    mut v_source_3287_: *mut crate::leanh::LeanObject,
    mut v_target_3288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: u8 = 0;
    let mut v_es_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3289_ = lean_array_get_size(v_source_3287_);
                v___x_3290_ = lean_nat_dec_lt(v_i_3286_, v___x_3289_);
                if v___x_3290_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3287_);
                    crate::leanh::lean_dec(v_i_3286_);
                    return v_target_3288_;
                } else {
                    v_es_3291_ = lean_array_fget(v_source_3287_, v_i_3286_);
                    v___x_3292_ = crate::leanh::lean_box(0);
                    v_source_3293_ = lean_array_fset(v_source_3287_, v_i_3286_, v___x_3292_);
                    v_target_3294_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_target_3288_, v_es_3291_);
                    v___x_3295_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3296_ = lean_nat_add(v_i_3286_, v___x_3295_);
                    crate::leanh::lean_dec(v_i_3286_);
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
    mut v_data_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3299_ = lean_array_get_size(v_data_3298_);
    v___x_3300_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3301_ = lean_nat_mul(v___x_3299_, v___x_3300_);
    v___x_3302_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3303_ = crate::leanh::lean_box(0);
    v___x_3304_ = lean_mk_array(v_nbuckets_3301_, v___x_3303_);
    v___x_3305_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v___x_3302_, v_data_3298_, v___x_3304_);
    return v___x_3305_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(
    mut v_m_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_b_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: u8 = 0;
    let mut v_val_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3309_ = crate::leanh::lean_ctor_get(v_m_3306_, 0);
                v_buckets_3310_ = crate::leanh::lean_ctor_get(v_m_3306_, 1);
                v_isSharedCheck_3353_ = (!crate::leanh::lean_is_exclusive(v_m_3306_)) as u8;
                if v_isSharedCheck_3353_ == 0 {
                    v___x_3312_ = v_m_3306_;
                    v_isShared_3313_ = v_isSharedCheck_3353_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3310_);
                    crate::leanh::lean_inc(v_size_3309_);
                    crate::leanh::lean_dec(v_m_3306_);
                    v___x_3312_ = crate::leanh::lean_box(0);
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
                    v___x_3329_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3330_ = lean_nat_add(v_size_3309_, v___x_3329_);
                    crate::leanh::lean_dec(v_size_3309_);
                    crate::leanh::lean_inc(v_bkt_3327_);
                    v___x_3331_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3331_, 0, v_a_3307_);
                    crate::leanh::lean_ctor_set(v___x_3331_, 1, v_b_3308_);
                    crate::leanh::lean_ctor_set(v___x_3331_, 2, v_bkt_3327_);
                    v_buckets_x27_3332_ =
                        lean_array_uset(v_buckets_3310_, v___x_3326_, v___x_3331_);
                    v___x_3333_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3334_ = lean_nat_mul(v_size_x27_3330_, v___x_3333_);
                    v___x_3335_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3336_ = lean_nat_div(v___x_3334_, v___x_3335_);
                    crate::leanh::lean_dec(v___x_3334_);
                    v___x_3337_ = lean_array_get_size(v_buckets_x27_3332_);
                    v___x_3338_ = lean_nat_dec_le(v___x_3336_, v___x_3337_);
                    crate::leanh::lean_dec(v___x_3336_);
                    if v___x_3338_ == 0 {
                        v_val_3339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_buckets_x27_3332_);
                        if v_isShared_3313_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3312_, 1, v_val_3339_);
                            crate::leanh::lean_ctor_set(v___x_3312_, 0, v_size_x27_3330_);
                            v___x_3341_ = v___x_3312_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3342_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3342_,
                                0,
                                v_size_x27_3330_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_val_3339_);
                            v___x_3341_ = v_reuseFailAlloc_3342_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3313_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3312_, 1, v_buckets_x27_3332_);
                            crate::leanh::lean_ctor_set(v___x_3312_, 0, v_size_x27_3330_);
                            v___x_3344_ = v___x_3312_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3345_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3345_,
                                0,
                                v_size_x27_3330_,
                            );
                            crate::leanh::lean_ctor_set(
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
                    crate::leanh::lean_inc(v_bkt_3327_);
                    v___x_3346_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3347_ =
                        lean_array_uset(v_buckets_3310_, v___x_3326_, v___x_3346_);
                    v___x_3348_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_3307_, v_b_3308_, v_bkt_3327_);
                    v___x_3349_ = lean_array_uset(v_buckets_x27_3347_, v___x_3326_, v___x_3348_);
                    if v_isShared_3313_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3312_, 1, v___x_3349_);
                        v___x_3351_ = v___x_3312_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3352_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_size_3309_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3352_, 1, v___x_3349_);
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
    mut v_val_3354_: *mut crate::leanh::LeanObject,
    mut v_x_3355_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3356_: u8 = 0;
    let mut v_head_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3355_) == 0 {
                    v___x_3356_ = 0;
                    return v___x_3356_;
                } else {
                    v_head_3357_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                    v_tail_3358_ = crate::leanh::lean_ctor_get(v_x_3355_, 1);
                    v_arg_3359_ = crate::leanh::lean_ctor_get(v_head_3357_, 0);
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
    mut v_val_3362_: *mut crate::leanh::LeanObject,
    mut v_x_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3364_: u8 = 0;
    let mut v_r_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3364_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(v_val_3362_, v_x_3363_);
    crate::leanh::lean_dec(v_x_3363_);
    crate::leanh::lean_dec_ref(v_val_3362_);
    v_r_3365_ = crate::leanh::lean_box((v_res_3364_) as usize);
    return v_r_3365_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3;
    v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5;
    v___x_3378_ = l_Lean_Name_append(v___x_3377_, v___x_3376_);
    return v___x_3378_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__7;
    v___x_3381_ = l_Lean_stringToMessageData(v___x_3380_);
    return v___x_3381_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__9;
    v___x_3384_ = l_Lean_stringToMessageData(v___x_3383_);
    return v___x_3384_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(
    mut v_e_3385_: *mut crate::leanh::LeanObject,
    mut v_ctx_3386_: *mut crate::leanh::LeanObject,
    mut v___x_3387_: *mut crate::leanh::LeanObject,
    mut v_as_3388_: *mut crate::leanh::LeanObject,
    mut v_sz_3389_: usize,
    mut v_i_3390_: usize,
    mut v_b_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: usize = 0;
    let mut v___x_3406_: usize = 0;
    let mut v___x_3408_: u8 = 0;
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3415_: u8 = 0;
    let mut v_fst_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3420_: u8 = 0;
    let mut v_map_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3437_: u8 = 0;
    let mut v___y_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3466_: u8 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_hasTheoryVar_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: u8 = 0;
    let mut v_options_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3483_: u8 = 0;
    let mut v_inheritedTraceOptions_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: u8 = 0;
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3504_: u8 = 0;
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3508_: u8 = 0;
    let mut v_reuseFailAlloc_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3513_: u8 = 0;
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3408_ = lean_usize_dec_lt(v_i_3390_, v_sz_3389_);
                if v___x_3408_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3387_);
                    crate::leanh::lean_dec_ref(v_ctx_3386_);
                    crate::leanh::lean_dec_ref(v_e_3385_);
                    v___x_3409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3409_, 0, v_b_3391_);
                    return v___x_3409_;
                } else {
                    v___x_3410_ = lean_st_ref_get(v___y_3392_);
                    v_snd_3411_ = crate::leanh::lean_ctor_get(v_b_3391_, 1);
                    v_fst_3412_ = crate::leanh::lean_ctor_get(v_b_3391_, 0);
                    v_isSharedCheck_3522_ = (!crate::leanh::lean_is_exclusive(v_b_3391_)) as u8;
                    if v_isSharedCheck_3522_ == 0 {
                        v___x_3414_ = v_b_3391_;
                        v_isShared_3415_ = v_isSharedCheck_3522_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3411_);
                        crate::leanh::lean_inc(v_fst_3412_);
                        crate::leanh::lean_dec(v_b_3391_);
                        v___x_3414_ = crate::leanh::lean_box(0);
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
                v_fst_3416_ = crate::leanh::lean_ctor_get(v_snd_3411_, 0);
                v_snd_3417_ = crate::leanh::lean_ctor_get(v_snd_3411_, 1);
                v_isSharedCheck_3521_ = (!crate::leanh::lean_is_exclusive(v_snd_3411_)) as u8;
                if v_isSharedCheck_3521_ == 0 {
                    v___x_3419_ = v_snd_3411_;
                    v_isShared_3420_ = v_isSharedCheck_3521_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3417_);
                    crate::leanh::lean_inc(v_fst_3416_);
                    crate::leanh::lean_dec(v_snd_3411_);
                    v___x_3419_ = crate::leanh::lean_box(0);
                    v_isShared_3420_ = v_isSharedCheck_3521_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_3432_ = lean_array_uget_borrowed(v_as_3388_, v_i_3390_);
                v___x_3433_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_3410_, v_a_3432_);
                crate::leanh::lean_dec(v___x_3410_);
                if crate::leanh::lean_obj_tag(v___x_3433_) == 1 {
                    v_val_3434_ = crate::leanh::lean_ctor_get(v___x_3433_, 0);
                    v_isSharedCheck_3518_ = (!crate::leanh::lean_is_exclusive(v___x_3433_)) as u8;
                    if v_isSharedCheck_3518_ == 0 {
                        v___x_3436_ = v___x_3433_;
                        v_isShared_3437_ = v_isSharedCheck_3518_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3434_);
                        crate::leanh::lean_dec(v___x_3433_);
                        v___x_3436_ = crate::leanh::lean_box(0);
                        v_isShared_3437_ = v_isSharedCheck_3518_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3433_);
                    crate::leanh::lean_del_object(v___x_3419_);
                    crate::leanh::lean_del_object(v___x_3414_);
                    v___x_3519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3519_, 0, v_fst_3416_);
                    crate::leanh::lean_ctor_set(v___x_3519_, 1, v_snd_3417_);
                    v___x_3520_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3520_, 0, v_fst_3412_);
                    crate::leanh::lean_ctor_set(v___x_3520_, 1, v___x_3519_);
                    v_a_3404_ = v___x_3520_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_3424_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3425_ = lean_nat_add(v_snd_3417_, v___x_3424_);
                crate::leanh::lean_dec(v_snd_3417_);
                if v_isShared_3420_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3419_, 1, v___x_3425_);
                    crate::leanh::lean_ctor_set(v___x_3419_, 0, v_candidates_3423_);
                    v___x_3427_ = v___x_3419_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_candidates_3423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3425_);
                    v___x_3427_ = v_reuseFailAlloc_3431_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3415_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3414_, 1, v___x_3427_);
                    crate::leanh::lean_ctor_set(v___x_3414_, 0, v_map_3422_);
                    v___x_3429_ = v___x_3414_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_map_3422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3427_);
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
                v_hasTheoryVar_3478_ = crate::leanh::lean_ctor_get(v_ctx_3386_, 1);
                crate::leanh::lean_inc_ref(v_hasTheoryVar_3478_);
                crate::leanh::lean_inc(v___y_3401_);
                crate::leanh::lean_inc_ref(v___y_3400_);
                crate::leanh::lean_inc(v___y_3399_);
                crate::leanh::lean_inc_ref(v___y_3398_);
                crate::leanh::lean_inc(v___y_3397_);
                crate::leanh::lean_inc_ref(v___y_3396_);
                crate::leanh::lean_inc(v___y_3395_);
                crate::leanh::lean_inc_ref(v___y_3394_);
                crate::leanh::lean_inc(v___y_3393_);
                crate::leanh::lean_inc(v___y_3392_);
                crate::leanh::lean_inc(v_val_3434_);
                v___x_3479_ = crate::leanh::lean_apply_12(
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
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3479_) == 0 {
                    v_a_3480_ = crate::leanh::lean_ctor_get(v___x_3479_, 0);
                    crate::leanh::lean_inc(v_a_3480_);
                    crate::leanh::lean_dec_ref_known(v___x_3479_, 1);
                    v___x_3481_ = (crate::leanh::lean_unbox(v_a_3480_) as u8);
                    crate::leanh::lean_dec(v_a_3480_);
                    if v___x_3481_ == 0 {
                        crate::leanh::lean_del_object(v___x_3436_);
                        crate::leanh::lean_dec(v_val_3434_);
                        v_map_3422_ = v_fst_3412_;
                        v_candidates_3423_ = v_fst_3416_;
                        state = 4;
                        continue;
                    } else {
                        v_options_3482_ = crate::leanh::lean_ctor_get(v___y_3400_, 2);
                        v_hasTrace_3483_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_3482_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3483_ == 0 {
                            crate::leanh::lean_del_object(v___x_3436_);
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
                                crate::leanh::lean_ctor_get(v___y_3400_, 13);
                            v___x_3485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__3;
                            v___x_3486_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__6);
                            v___x_3487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3484_,
                                v_options_3482_,
                                v___x_3486_,
                            );
                            if v___x_3487_ == 0 {
                                crate::leanh::lean_del_object(v___x_3436_);
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
                                crate::leanh::lean_inc(v_val_3434_);
                                v___x_3488_ = l_Lean_MessageData_ofExpr(v_val_3434_);
                                v___x_3489_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__8);
                                v___x_3490_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3490_, 0, v___x_3488_);
                                crate::leanh::lean_ctor_set(v___x_3490_, 1, v___x_3489_);
                                crate::leanh::lean_inc_ref(v___x_3387_);
                                v___x_3491_ = l_Lean_MessageData_ofExpr(v___x_3387_);
                                v___x_3492_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3492_, 0, v___x_3490_);
                                crate::leanh::lean_ctor_set(v___x_3492_, 1, v___x_3491_);
                                v___x_3493_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__10);
                                v___x_3494_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3494_, 0, v___x_3492_);
                                crate::leanh::lean_ctor_set(v___x_3494_, 1, v___x_3493_);
                                crate::leanh::lean_inc(v_snd_3417_);
                                v___x_3495_ = l_Nat_reprFast(v_snd_3417_);
                                if v_isShared_3437_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_3436_, 3);
                                    crate::leanh::lean_ctor_set(v___x_3436_, 0, v___x_3495_);
                                    v___x_3497_ = v___x_3436_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3509_ =
                                        crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
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
                    crate::leanh::lean_del_object(v___x_3436_);
                    crate::leanh::lean_dec(v_val_3434_);
                    crate::leanh::lean_del_object(v___x_3419_);
                    crate::leanh::lean_dec(v_snd_3417_);
                    crate::leanh::lean_dec(v_fst_3416_);
                    crate::leanh::lean_del_object(v___x_3414_);
                    crate::leanh::lean_dec(v_fst_3412_);
                    crate::leanh::lean_dec_ref(v___x_3387_);
                    crate::leanh::lean_dec_ref(v_ctx_3386_);
                    crate::leanh::lean_dec_ref(v_e_3385_);
                    v_a_3510_ = crate::leanh::lean_ctor_get(v___x_3479_, 0);
                    v_isSharedCheck_3517_ = (!crate::leanh::lean_is_exclusive(v___x_3479_)) as u8;
                    if v_isSharedCheck_3517_ == 0 {
                        v___x_3512_ = v___x_3479_;
                        v_isShared_3513_ = v_isSharedCheck_3517_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3510_);
                        crate::leanh::lean_dec(v___x_3479_);
                        v___x_3512_ = crate::leanh::lean_box(0);
                        v_isShared_3513_ = v_isSharedCheck_3517_;
                        state = 16;
                        continue;
                    }
                }
            }
            8 => {
                crate::leanh::lean_inc_ref_n(v_e_3385_, 2);
                crate::leanh::lean_inc(v_val_3434_);
                v___x_3449_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3449_, 0, v_val_3434_);
                crate::leanh::lean_ctor_set(v___x_3449_, 1, v_e_3385_);
                v___x_3450_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey(
                    v_e_3385_,
                    v_snd_3417_,
                    v___y_3445_,
                    v___y_3446_,
                    v___y_3447_,
                    v___y_3448_,
                );
                if crate::leanh::lean_obj_tag(v___x_3450_) == 0 {
                    v_a_3451_ = crate::leanh::lean_ctor_get(v___x_3450_, 0);
                    crate::leanh::lean_inc(v_a_3451_);
                    crate::leanh::lean_dec_ref_known(v___x_3450_, 1);
                    v___x_3452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_fst_3412_, v_a_3451_);
                    if crate::leanh::lean_obj_tag(v___x_3452_) == 1 {
                        v_val_3453_ = crate::leanh::lean_ctor_get(v___x_3452_, 0);
                        crate::leanh::lean_inc(v_val_3453_);
                        crate::leanh::lean_dec_ref_known(v___x_3452_, 1);
                        v___x_3454_ = l_List_any___at___00Lean_Meta_Grind_mbtc_spec__3(
                            v_val_3434_,
                            v_val_3453_,
                        );
                        if v___x_3454_ == 0 {
                            crate::leanh::lean_inc(v_snd_3417_);
                            crate::leanh::lean_inc_ref(v___x_3449_);
                            crate::leanh::lean_inc_ref(v_ctx_3386_);
                            v___x_3455_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4___redArg(v_ctx_3386_, v_val_3434_, v___x_3449_, v_snd_3417_, v_val_3453_, v_fst_3416_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
                            if crate::leanh::lean_obj_tag(v___x_3455_) == 0 {
                                v_a_3456_ = crate::leanh::lean_ctor_get(v___x_3455_, 0);
                                crate::leanh::lean_inc(v_a_3456_);
                                crate::leanh::lean_dec_ref_known(v___x_3455_, 1);
                                v___x_3457_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3457_, 0, v___x_3449_);
                                crate::leanh::lean_ctor_set(v___x_3457_, 1, v_val_3453_);
                                v___x_3458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_3412_, v_a_3451_, v___x_3457_);
                                v_map_3422_ = v___x_3458_;
                                v_candidates_3423_ = v_a_3456_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_3453_);
                                crate::leanh::lean_dec(v_a_3451_);
                                crate::leanh::lean_dec_ref_known(v___x_3449_, 2);
                                crate::leanh::lean_del_object(v___x_3419_);
                                crate::leanh::lean_dec(v_snd_3417_);
                                crate::leanh::lean_del_object(v___x_3414_);
                                crate::leanh::lean_dec(v_fst_3412_);
                                crate::leanh::lean_dec_ref(v___x_3387_);
                                crate::leanh::lean_dec_ref(v_ctx_3386_);
                                crate::leanh::lean_dec_ref(v_e_3385_);
                                v_a_3459_ = crate::leanh::lean_ctor_get(v___x_3455_, 0);
                                v_isSharedCheck_3466_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3455_)) as u8;
                                if v_isSharedCheck_3466_ == 0 {
                                    v___x_3461_ = v___x_3455_;
                                    v_isShared_3462_ = v_isSharedCheck_3466_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3459_);
                                    crate::leanh::lean_dec(v___x_3455_);
                                    v___x_3461_ = crate::leanh::lean_box(0);
                                    v_isShared_3462_ = v_isSharedCheck_3466_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_3453_);
                            crate::leanh::lean_dec(v_a_3451_);
                            crate::leanh::lean_dec_ref_known(v___x_3449_, 2);
                            crate::leanh::lean_dec(v_val_3434_);
                            v_map_3422_ = v_fst_3412_;
                            v_candidates_3423_ = v_fst_3416_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3452_);
                        crate::leanh::lean_dec(v_val_3434_);
                        v___x_3467_ = crate::leanh::lean_box(0);
                        v___x_3468_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3468_, 0, v___x_3449_);
                        crate::leanh::lean_ctor_set(v___x_3468_, 1, v___x_3467_);
                        v___x_3469_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(v_fst_3412_, v_a_3451_, v___x_3468_);
                        v_map_3422_ = v___x_3469_;
                        v_candidates_3423_ = v_fst_3416_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3449_, 2);
                    crate::leanh::lean_dec(v_val_3434_);
                    crate::leanh::lean_del_object(v___x_3419_);
                    crate::leanh::lean_dec(v_snd_3417_);
                    crate::leanh::lean_dec(v_fst_3416_);
                    crate::leanh::lean_del_object(v___x_3414_);
                    crate::leanh::lean_dec(v_fst_3412_);
                    crate::leanh::lean_dec_ref(v___x_3387_);
                    crate::leanh::lean_dec_ref(v_ctx_3386_);
                    crate::leanh::lean_dec_ref(v_e_3385_);
                    v_a_3470_ = crate::leanh::lean_ctor_get(v___x_3450_, 0);
                    v_isSharedCheck_3477_ = (!crate::leanh::lean_is_exclusive(v___x_3450_)) as u8;
                    if v_isSharedCheck_3477_ == 0 {
                        v___x_3472_ = v___x_3450_;
                        v_isShared_3473_ = v_isSharedCheck_3477_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3470_);
                        crate::leanh::lean_dec(v___x_3450_);
                        v___x_3472_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
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
                    v_reuseFailAlloc_3476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
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
                v___x_3499_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3499_, 0, v___x_3494_);
                crate::leanh::lean_ctor_set(v___x_3499_, 1, v___x_3498_);
                v___x_3500_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(
                    v___x_3485_,
                    v___x_3499_,
                    v___y_3398_,
                    v___y_3399_,
                    v___y_3400_,
                    v___y_3401_,
                );
                if crate::leanh::lean_obj_tag(v___x_3500_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3500_, 1);
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
                    crate::leanh::lean_dec(v_val_3434_);
                    crate::leanh::lean_del_object(v___x_3419_);
                    crate::leanh::lean_dec(v_snd_3417_);
                    crate::leanh::lean_dec(v_fst_3416_);
                    crate::leanh::lean_del_object(v___x_3414_);
                    crate::leanh::lean_dec(v_fst_3412_);
                    crate::leanh::lean_dec_ref(v___x_3387_);
                    crate::leanh::lean_dec_ref(v_ctx_3386_);
                    crate::leanh::lean_dec_ref(v_e_3385_);
                    v_a_3501_ = crate::leanh::lean_ctor_get(v___x_3500_, 0);
                    v_isSharedCheck_3508_ = (!crate::leanh::lean_is_exclusive(v___x_3500_)) as u8;
                    if v_isSharedCheck_3508_ == 0 {
                        v___x_3503_ = v___x_3500_;
                        v_isShared_3504_ = v_isSharedCheck_3508_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3501_);
                        crate::leanh::lean_dec(v___x_3500_);
                        v___x_3503_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
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
                    v_reuseFailAlloc_3516_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_3523_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_ctx_3524_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_3525_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_as_3526_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_sz_3527_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_i_3528_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_b_3529_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_3530_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_3531_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_3532_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3533_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3534_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3535_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3536_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3537_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3538_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3539_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3540_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_sz_boxed_3541_: usize = 0;
    let mut v_i_boxed_3542_: usize = 0;
    let mut v_res_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3541_ = crate::leanh::lean_unbox_usize(v_sz_3527_);
    crate::leanh::lean_dec(v_sz_3527_);
    v_i_boxed_3542_ = crate::leanh::lean_unbox_usize(v_i_3528_);
    crate::leanh::lean_dec(v_i_3528_);
    v_res_3543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_e_3523_, v_ctx_3524_, v___x_3525_, v_as_3526_, v_sz_boxed_3541_, v_i_boxed_3542_, v_b_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
    crate::leanh::lean_dec(v___y_3539_);
    crate::leanh::lean_dec_ref(v___y_3538_);
    crate::leanh::lean_dec(v___y_3537_);
    crate::leanh::lean_dec_ref(v___y_3536_);
    crate::leanh::lean_dec(v___y_3535_);
    crate::leanh::lean_dec_ref(v___y_3534_);
    crate::leanh::lean_dec(v___y_3533_);
    crate::leanh::lean_dec_ref(v___y_3532_);
    crate::leanh::lean_dec(v___y_3531_);
    crate::leanh::lean_dec(v___y_3530_);
    crate::leanh::lean_dec_ref(v_as_3526_);
    return v_res_3543_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(
    mut v_ctx_3544_: *mut crate::leanh::LeanObject,
    mut v_as_3545_: *mut crate::leanh::LeanObject,
    mut v_sz_3546_: usize,
    mut v_i_3547_: usize,
    mut v_b_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
    mut v___y_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
    mut v___y_3552_: *mut crate::leanh::LeanObject,
    mut v___y_3553_: *mut crate::leanh::LeanObject,
    mut v___y_3554_: *mut crate::leanh::LeanObject,
    mut v___y_3555_: *mut crate::leanh::LeanObject,
    mut v___y_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3560_: u8 = 0;
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v_fst_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3570_: u8 = 0;
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: usize = 0;
    let mut v___x_3577_: usize = 0;
    let mut v_reuseFailAlloc_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: u8 = 0;
    let mut v___x_3589_: u8 = 0;
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: u8 = 0;
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInterpreted_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    let mut v___x_3602_: u8 = 0;
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3612_: usize = 0;
    let mut v___x_3613_: usize = 0;
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3621_: u8 = 0;
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3625_: u8 = 0;
    let mut v_unused_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3630_: u8 = 0;
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_a_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v_a_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3655_: u8 = 0;
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: u8 = 0;
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v_unused_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3560_ = lean_usize_dec_lt(v_i_3547_, v_sz_3546_);
                if v___x_3560_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_3544_);
                    v___x_3561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3561_, 0, v_b_3548_);
                    return v___x_3561_;
                } else {
                    v_snd_3562_ = crate::leanh::lean_ctor_get(v_b_3548_, 1);
                    v_isSharedCheck_3663_ = (!crate::leanh::lean_is_exclusive(v_b_3548_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v_unused_3664_ = crate::leanh::lean_ctor_get(v_b_3548_, 0);
                        crate::leanh::lean_dec(v_unused_3664_);
                        v___x_3564_ = v_b_3548_;
                        v_isShared_3565_ = v_isSharedCheck_3663_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3562_);
                        crate::leanh::lean_dec(v_b_3548_);
                        v___x_3564_ = crate::leanh::lean_box(0);
                        v_isShared_3565_ = v_isSharedCheck_3663_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3566_ = crate::leanh::lean_ctor_get(v_snd_3562_, 0);
                v_snd_3567_ = crate::leanh::lean_ctor_get(v_snd_3562_, 1);
                v_isSharedCheck_3662_ = (!crate::leanh::lean_is_exclusive(v_snd_3562_)) as u8;
                if v_isSharedCheck_3662_ == 0 {
                    v___x_3569_ = v_snd_3562_;
                    v_isShared_3570_ = v_isSharedCheck_3662_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3567_);
                    crate::leanh::lean_inc(v_fst_3566_);
                    crate::leanh::lean_dec(v_snd_3562_);
                    v___x_3569_ = crate::leanh::lean_box(0);
                    v_isShared_3570_ = v_isSharedCheck_3662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3571_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_3569_, 1, v_a_3573_);
                    crate::leanh::lean_ctor_set(v___x_3569_, 0, v___x_3571_);
                    v___x_3575_ = v___x_3569_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3571_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_a_3573_);
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
                    crate::leanh::lean_ctor_set(v___x_3564_, 1, v_snd_3567_);
                    crate::leanh::lean_ctor_set(v___x_3564_, 0, v_fst_3566_);
                    v___x_3582_ = v___x_3564_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_fst_3566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_snd_3567_);
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
                v___x_3585_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3585_, 0, v_fst_3566_);
                crate::leanh::lean_ctor_set(v___x_3585_, 1, v_snd_3567_);
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
                        crate::leanh::lean_del_object(v___x_3564_);
                        crate::leanh::lean_inc(v_a_3586_);
                        v___x_3590_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                            v_a_3586_,
                            v___y_3549_,
                            v___y_3555_,
                            v___y_3556_,
                            v___y_3557_,
                            v___y_3558_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3590_) == 0 {
                            v_a_3591_ = crate::leanh::lean_ctor_get(v___x_3590_, 0);
                            crate::leanh::lean_inc(v_a_3591_);
                            crate::leanh::lean_dec_ref_known(v___x_3590_, 1);
                            v___x_3592_ = (crate::leanh::lean_unbox(v_a_3591_) as u8);
                            crate::leanh::lean_dec(v_a_3591_);
                            if v___x_3592_ == 0 {
                                v___x_3593_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3593_, 0, v_fst_3566_);
                                crate::leanh::lean_ctor_set(v___x_3593_, 1, v_snd_3567_);
                                v_a_3573_ = v___x_3593_;
                                state = 3;
                                continue;
                            } else {
                                v_isInterpreted_3594_ = crate::leanh::lean_ctor_get(v_ctx_3544_, 0);
                                crate::leanh::lean_inc_ref(v_isInterpreted_3594_);
                                crate::leanh::lean_inc(v___y_3558_);
                                crate::leanh::lean_inc_ref(v___y_3557_);
                                crate::leanh::lean_inc(v___y_3556_);
                                crate::leanh::lean_inc_ref(v___y_3555_);
                                crate::leanh::lean_inc(v___y_3554_);
                                crate::leanh::lean_inc_ref(v___y_3553_);
                                crate::leanh::lean_inc(v___y_3552_);
                                crate::leanh::lean_inc_ref(v___y_3551_);
                                crate::leanh::lean_inc(v___y_3550_);
                                crate::leanh::lean_inc(v___y_3549_);
                                crate::leanh::lean_inc(v_a_3586_);
                                v___x_3595_ = crate::leanh::lean_apply_12(
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
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_3595_) == 0 {
                                    v_a_3596_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                                    crate::leanh::lean_inc(v_a_3596_);
                                    crate::leanh::lean_dec_ref_known(v___x_3595_, 1);
                                    v___x_3597_ = (crate::leanh::lean_unbox(v_a_3596_) as u8);
                                    crate::leanh::lean_dec(v_a_3596_);
                                    if v___x_3597_ == 0 {
                                        v___x_3598_ = l_Lean_Expr_getAppFn(v_a_3586_);
                                        crate::leanh::lean_inc_ref(v___x_3598_);
                                        v___x_3599_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_3598_, v___y_3557_, v___y_3558_);
                                        if crate::leanh::lean_obj_tag(v___x_3599_) == 0 {
                                            v_a_3600_ = crate::leanh::lean_ctor_get(v___x_3599_, 0);
                                            crate::leanh::lean_inc(v_a_3600_);
                                            crate::leanh::lean_dec_ref_known(v___x_3599_, 1);
                                            v___x_3601_ =
                                                (crate::leanh::lean_unbox(v_a_3600_) as u8);
                                            crate::leanh::lean_dec(v_a_3600_);
                                            if v___x_3601_ == 0 {
                                                v___x_3602_ =
                                                    l_Lean_Meta_Grind_isCastLikeFn(v___x_3598_);
                                                if v___x_3602_ == 0 {
                                                    v___x_3603_ =
                                                        crate::leanh::lean_unsigned_to_nat(0);
                                                    v_dummy_3604_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
                                                    v_nargs_3605_ =
                                                        l_Lean_Expr_getAppNumArgs(v_a_3586_);
                                                    crate::leanh::lean_inc(v_nargs_3605_);
                                                    v___x_3606_ =
                                                        lean_mk_array(v_nargs_3605_, v_dummy_3604_);
                                                    v___x_3607_ =
                                                        crate::leanh::lean_unsigned_to_nat(1);
                                                    v___x_3608_ =
                                                        lean_nat_sub(v_nargs_3605_, v___x_3607_);
                                                    crate::leanh::lean_dec(v_nargs_3605_);
                                                    crate::leanh::lean_inc_n(v_a_3586_, 2);
                                                    v___x_3609_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3586_, v___x_3606_, v___x_3608_);
                                                    v___x_3610_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3610_,
                                                        0,
                                                        v_snd_3567_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3610_,
                                                        1,
                                                        v___x_3603_,
                                                    );
                                                    v___x_3611_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3611_,
                                                        0,
                                                        v_fst_3566_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3611_,
                                                        1,
                                                        v___x_3610_,
                                                    );
                                                    v_sz_3612_ = lean_array_size(v___x_3609_);
                                                    v___x_3613_ = 0usize;
                                                    crate::leanh::lean_inc_ref(v_ctx_3544_);
                                                    v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_3586_, v_ctx_3544_, v___x_3598_, v___x_3609_, v_sz_3612_, v___x_3613_, v___x_3611_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
                                                    crate::leanh::lean_dec_ref(v___x_3609_);
                                                    if crate::leanh::lean_obj_tag(v___x_3614_) == 0
                                                    {
                                                        v_a_3615_ = crate::leanh::lean_ctor_get(
                                                            v___x_3614_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_3615_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3614_,
                                                            1,
                                                        );
                                                        v_snd_3616_ = crate::leanh::lean_ctor_get(
                                                            v_a_3615_, 1,
                                                        );
                                                        crate::leanh::lean_inc(v_snd_3616_);
                                                        v_fst_3617_ = crate::leanh::lean_ctor_get(
                                                            v_a_3615_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_fst_3617_);
                                                        crate::leanh::lean_dec(v_a_3615_);
                                                        v_fst_3618_ = crate::leanh::lean_ctor_get(
                                                            v_snd_3616_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3625_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v_snd_3616_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3625_ == 0 {
                                                            v_unused_3626_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_snd_3616_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_dec(v_unused_3626_);
                                                            v___x_3620_ = v_snd_3616_;
                                                            v_isShared_3621_ =
                                                                v_isSharedCheck_3625_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_fst_3618_);
                                                            crate::leanh::lean_dec(v_snd_3616_);
                                                            v___x_3620_ = crate::leanh::lean_box(0);
                                                            v_isShared_3621_ =
                                                                v_isSharedCheck_3625_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_del_object(v___x_3569_);
                                                        crate::leanh::lean_dec_ref(v_ctx_3544_);
                                                        v_a_3627_ = crate::leanh::lean_ctor_get(
                                                            v___x_3614_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3634_ =
                                                            (!crate::leanh::lean_is_exclusive(
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
                                                            crate::leanh::lean_inc(v_a_3627_);
                                                            crate::leanh::lean_dec(v___x_3614_);
                                                            v___x_3629_ = crate::leanh::lean_box(0);
                                                            v_isShared_3630_ =
                                                                v_isSharedCheck_3634_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_3598_);
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3598_);
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3598_);
                                            crate::leanh::lean_del_object(v___x_3569_);
                                            crate::leanh::lean_dec(v_snd_3567_);
                                            crate::leanh::lean_dec(v_fst_3566_);
                                            crate::leanh::lean_dec_ref(v_ctx_3544_);
                                            v_a_3635_ = crate::leanh::lean_ctor_get(v___x_3599_, 0);
                                            v_isSharedCheck_3642_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3599_))
                                                    as u8;
                                            if v_isSharedCheck_3642_ == 0 {
                                                v___x_3637_ = v___x_3599_;
                                                v_isShared_3638_ = v_isSharedCheck_3642_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3635_);
                                                crate::leanh::lean_dec(v___x_3599_);
                                                v___x_3637_ = crate::leanh::lean_box(0);
                                                v_isShared_3638_ = v_isSharedCheck_3642_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_3643_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3643_, 0, v_fst_3566_);
                                        crate::leanh::lean_ctor_set(v___x_3643_, 1, v_snd_3567_);
                                        v_a_3573_ = v___x_3643_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_3569_);
                                    crate::leanh::lean_dec(v_snd_3567_);
                                    crate::leanh::lean_dec(v_fst_3566_);
                                    crate::leanh::lean_dec_ref(v_ctx_3544_);
                                    v_a_3644_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                                    v_isSharedCheck_3651_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3595_)) as u8;
                                    if v_isSharedCheck_3651_ == 0 {
                                        v___x_3646_ = v___x_3595_;
                                        v_isShared_3647_ = v_isSharedCheck_3651_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3644_);
                                        crate::leanh::lean_dec(v___x_3595_);
                                        v___x_3646_ = crate::leanh::lean_box(0);
                                        v_isShared_3647_ = v_isSharedCheck_3651_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3569_);
                            crate::leanh::lean_dec(v_snd_3567_);
                            crate::leanh::lean_dec(v_fst_3566_);
                            crate::leanh::lean_dec_ref(v_ctx_3544_);
                            v_a_3652_ = crate::leanh::lean_ctor_get(v___x_3590_, 0);
                            v_isSharedCheck_3659_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3590_)) as u8;
                            if v_isSharedCheck_3659_ == 0 {
                                v___x_3654_ = v___x_3590_;
                                v_isShared_3655_ = v_isSharedCheck_3659_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3652_);
                                crate::leanh::lean_dec(v___x_3590_);
                                v___x_3654_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_3620_, 1, v_fst_3618_);
                    crate::leanh::lean_ctor_set(v___x_3620_, 0, v_fst_3617_);
                    v___x_3623_ = v___x_3620_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3624_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_fst_3617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_fst_3618_);
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
                    v_reuseFailAlloc_3633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
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
                    v_reuseFailAlloc_3641_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
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
                    v_reuseFailAlloc_3650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
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
                    v_reuseFailAlloc_3658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
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
    mut v_ctx_3665_: *mut crate::leanh::LeanObject,
    mut v_as_3666_: *mut crate::leanh::LeanObject,
    mut v_sz_3667_: *mut crate::leanh::LeanObject,
    mut v_i_3668_: *mut crate::leanh::LeanObject,
    mut v_b_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
    mut v___y_3674_: *mut crate::leanh::LeanObject,
    mut v___y_3675_: *mut crate::leanh::LeanObject,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
    mut v___y_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3681_: usize = 0;
    let mut v_i_boxed_3682_: usize = 0;
    let mut v_res_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3681_ = crate::leanh::lean_unbox_usize(v_sz_3667_);
    crate::leanh::lean_dec(v_sz_3667_);
    v_i_boxed_3682_ = crate::leanh::lean_unbox_usize(v_i_3668_);
    crate::leanh::lean_dec(v_i_3668_);
    v_res_3683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15_spec__20(v_ctx_3665_, v_as_3666_, v_sz_boxed_3681_, v_i_boxed_3682_, v_b_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
    crate::leanh::lean_dec(v___y_3679_);
    crate::leanh::lean_dec_ref(v___y_3678_);
    crate::leanh::lean_dec(v___y_3677_);
    crate::leanh::lean_dec_ref(v___y_3676_);
    crate::leanh::lean_dec(v___y_3675_);
    crate::leanh::lean_dec_ref(v___y_3674_);
    crate::leanh::lean_dec(v___y_3673_);
    crate::leanh::lean_dec_ref(v___y_3672_);
    crate::leanh::lean_dec(v___y_3671_);
    crate::leanh::lean_dec(v___y_3670_);
    crate::leanh::lean_dec_ref(v_as_3666_);
    return v_res_3683_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(
    mut v_ctx_3684_: *mut crate::leanh::LeanObject,
    mut v_as_3685_: *mut crate::leanh::LeanObject,
    mut v_sz_3686_: usize,
    mut v_i_3687_: usize,
    mut v_b_3688_: *mut crate::leanh::LeanObject,
    mut v___y_3689_: *mut crate::leanh::LeanObject,
    mut v___y_3690_: *mut crate::leanh::LeanObject,
    mut v___y_3691_: *mut crate::leanh::LeanObject,
    mut v___y_3692_: *mut crate::leanh::LeanObject,
    mut v___y_3693_: *mut crate::leanh::LeanObject,
    mut v___y_3694_: *mut crate::leanh::LeanObject,
    mut v___y_3695_: *mut crate::leanh::LeanObject,
    mut v___y_3696_: *mut crate::leanh::LeanObject,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3700_: u8 = 0;
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v_fst_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3710_: u8 = 0;
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: usize = 0;
    let mut v___x_3717_: usize = 0;
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3728_: u8 = 0;
    let mut v___x_3729_: u8 = 0;
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: u8 = 0;
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInterpreted_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3752_: usize = 0;
    let mut v___x_3753_: usize = 0;
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3761_: u8 = 0;
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3765_: u8 = 0;
    let mut v_unused_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3770_: u8 = 0;
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3774_: u8 = 0;
    let mut v_a_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3778_: u8 = 0;
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3787_: u8 = 0;
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3791_: u8 = 0;
    let mut v_a_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: u8 = 0;
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_unused_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3700_ = lean_usize_dec_lt(v_i_3687_, v_sz_3686_);
                if v___x_3700_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_3684_);
                    v___x_3701_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3701_, 0, v_b_3688_);
                    return v___x_3701_;
                } else {
                    v_snd_3702_ = crate::leanh::lean_ctor_get(v_b_3688_, 1);
                    v_isSharedCheck_3803_ = (!crate::leanh::lean_is_exclusive(v_b_3688_)) as u8;
                    if v_isSharedCheck_3803_ == 0 {
                        v_unused_3804_ = crate::leanh::lean_ctor_get(v_b_3688_, 0);
                        crate::leanh::lean_dec(v_unused_3804_);
                        v___x_3704_ = v_b_3688_;
                        v_isShared_3705_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3702_);
                        crate::leanh::lean_dec(v_b_3688_);
                        v___x_3704_ = crate::leanh::lean_box(0);
                        v_isShared_3705_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3706_ = crate::leanh::lean_ctor_get(v_snd_3702_, 0);
                v_snd_3707_ = crate::leanh::lean_ctor_get(v_snd_3702_, 1);
                v_isSharedCheck_3802_ = (!crate::leanh::lean_is_exclusive(v_snd_3702_)) as u8;
                if v_isSharedCheck_3802_ == 0 {
                    v___x_3709_ = v_snd_3702_;
                    v_isShared_3710_ = v_isSharedCheck_3802_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3707_);
                    crate::leanh::lean_inc(v_fst_3706_);
                    crate::leanh::lean_dec(v_snd_3702_);
                    v___x_3709_ = crate::leanh::lean_box(0);
                    v_isShared_3710_ = v_isSharedCheck_3802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3711_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_3709_, 1, v_a_3713_);
                    crate::leanh::lean_ctor_set(v___x_3709_, 0, v___x_3711_);
                    v___x_3715_ = v___x_3709_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_a_3713_);
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
                    crate::leanh::lean_ctor_set(v___x_3704_, 1, v_snd_3707_);
                    crate::leanh::lean_ctor_set(v___x_3704_, 0, v_fst_3706_);
                    v___x_3722_ = v___x_3704_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3723_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_fst_3706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_snd_3707_);
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
                v___x_3725_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3725_, 0, v_fst_3706_);
                crate::leanh::lean_ctor_set(v___x_3725_, 1, v_snd_3707_);
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
                        crate::leanh::lean_del_object(v___x_3704_);
                        crate::leanh::lean_inc(v_a_3726_);
                        v___x_3730_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                            v_a_3726_,
                            v___y_3689_,
                            v___y_3695_,
                            v___y_3696_,
                            v___y_3697_,
                            v___y_3698_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3730_) == 0 {
                            v_a_3731_ = crate::leanh::lean_ctor_get(v___x_3730_, 0);
                            crate::leanh::lean_inc(v_a_3731_);
                            crate::leanh::lean_dec_ref_known(v___x_3730_, 1);
                            v___x_3732_ = (crate::leanh::lean_unbox(v_a_3731_) as u8);
                            crate::leanh::lean_dec(v_a_3731_);
                            if v___x_3732_ == 0 {
                                v___x_3733_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3733_, 0, v_fst_3706_);
                                crate::leanh::lean_ctor_set(v___x_3733_, 1, v_snd_3707_);
                                v_a_3713_ = v___x_3733_;
                                state = 3;
                                continue;
                            } else {
                                v_isInterpreted_3734_ = crate::leanh::lean_ctor_get(v_ctx_3684_, 0);
                                crate::leanh::lean_inc_ref(v_isInterpreted_3734_);
                                crate::leanh::lean_inc(v___y_3698_);
                                crate::leanh::lean_inc_ref(v___y_3697_);
                                crate::leanh::lean_inc(v___y_3696_);
                                crate::leanh::lean_inc_ref(v___y_3695_);
                                crate::leanh::lean_inc(v___y_3694_);
                                crate::leanh::lean_inc_ref(v___y_3693_);
                                crate::leanh::lean_inc(v___y_3692_);
                                crate::leanh::lean_inc_ref(v___y_3691_);
                                crate::leanh::lean_inc(v___y_3690_);
                                crate::leanh::lean_inc(v___y_3689_);
                                crate::leanh::lean_inc(v_a_3726_);
                                v___x_3735_ = crate::leanh::lean_apply_12(
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
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_3735_) == 0 {
                                    v_a_3736_ = crate::leanh::lean_ctor_get(v___x_3735_, 0);
                                    crate::leanh::lean_inc(v_a_3736_);
                                    crate::leanh::lean_dec_ref_known(v___x_3735_, 1);
                                    v___x_3737_ = (crate::leanh::lean_unbox(v_a_3736_) as u8);
                                    crate::leanh::lean_dec(v_a_3736_);
                                    if v___x_3737_ == 0 {
                                        v___x_3738_ = l_Lean_Expr_getAppFn(v_a_3726_);
                                        crate::leanh::lean_inc_ref(v___x_3738_);
                                        v___x_3739_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_3738_, v___y_3697_, v___y_3698_);
                                        if crate::leanh::lean_obj_tag(v___x_3739_) == 0 {
                                            v_a_3740_ = crate::leanh::lean_ctor_get(v___x_3739_, 0);
                                            crate::leanh::lean_inc(v_a_3740_);
                                            crate::leanh::lean_dec_ref_known(v___x_3739_, 1);
                                            v___x_3741_ =
                                                (crate::leanh::lean_unbox(v_a_3740_) as u8);
                                            crate::leanh::lean_dec(v_a_3740_);
                                            if v___x_3741_ == 0 {
                                                v___x_3742_ =
                                                    l_Lean_Meta_Grind_isCastLikeFn(v___x_3738_);
                                                if v___x_3742_ == 0 {
                                                    v___x_3743_ =
                                                        crate::leanh::lean_unsigned_to_nat(0);
                                                    v_dummy_3744_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
                                                    v_nargs_3745_ =
                                                        l_Lean_Expr_getAppNumArgs(v_a_3726_);
                                                    crate::leanh::lean_inc(v_nargs_3745_);
                                                    v___x_3746_ =
                                                        lean_mk_array(v_nargs_3745_, v_dummy_3744_);
                                                    v___x_3747_ =
                                                        crate::leanh::lean_unsigned_to_nat(1);
                                                    v___x_3748_ =
                                                        lean_nat_sub(v_nargs_3745_, v___x_3747_);
                                                    crate::leanh::lean_dec(v_nargs_3745_);
                                                    crate::leanh::lean_inc_n(v_a_3726_, 2);
                                                    v___x_3749_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3726_, v___x_3746_, v___x_3748_);
                                                    v___x_3750_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3750_,
                                                        0,
                                                        v_snd_3707_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3750_,
                                                        1,
                                                        v___x_3743_,
                                                    );
                                                    v___x_3751_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3751_,
                                                        0,
                                                        v_fst_3706_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3751_,
                                                        1,
                                                        v___x_3750_,
                                                    );
                                                    v_sz_3752_ = lean_array_size(v___x_3749_);
                                                    v___x_3753_ = 0usize;
                                                    crate::leanh::lean_inc_ref(v_ctx_3684_);
                                                    v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_3726_, v_ctx_3684_, v___x_3738_, v___x_3749_, v_sz_3752_, v___x_3753_, v___x_3751_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
                                                    crate::leanh::lean_dec_ref(v___x_3749_);
                                                    if crate::leanh::lean_obj_tag(v___x_3754_) == 0
                                                    {
                                                        v_a_3755_ = crate::leanh::lean_ctor_get(
                                                            v___x_3754_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_3755_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3754_,
                                                            1,
                                                        );
                                                        v_snd_3756_ = crate::leanh::lean_ctor_get(
                                                            v_a_3755_, 1,
                                                        );
                                                        crate::leanh::lean_inc(v_snd_3756_);
                                                        v_fst_3757_ = crate::leanh::lean_ctor_get(
                                                            v_a_3755_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_fst_3757_);
                                                        crate::leanh::lean_dec(v_a_3755_);
                                                        v_fst_3758_ = crate::leanh::lean_ctor_get(
                                                            v_snd_3756_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3765_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v_snd_3756_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3765_ == 0 {
                                                            v_unused_3766_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_snd_3756_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_dec(v_unused_3766_);
                                                            v___x_3760_ = v_snd_3756_;
                                                            v_isShared_3761_ =
                                                                v_isSharedCheck_3765_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_fst_3758_);
                                                            crate::leanh::lean_dec(v_snd_3756_);
                                                            v___x_3760_ = crate::leanh::lean_box(0);
                                                            v_isShared_3761_ =
                                                                v_isSharedCheck_3765_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_del_object(v___x_3709_);
                                                        crate::leanh::lean_dec_ref(v_ctx_3684_);
                                                        v_a_3767_ = crate::leanh::lean_ctor_get(
                                                            v___x_3754_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3774_ =
                                                            (!crate::leanh::lean_is_exclusive(
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
                                                            crate::leanh::lean_inc(v_a_3767_);
                                                            crate::leanh::lean_dec(v___x_3754_);
                                                            v___x_3769_ = crate::leanh::lean_box(0);
                                                            v_isShared_3770_ =
                                                                v_isSharedCheck_3774_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_3738_);
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3738_);
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3738_);
                                            crate::leanh::lean_del_object(v___x_3709_);
                                            crate::leanh::lean_dec(v_snd_3707_);
                                            crate::leanh::lean_dec(v_fst_3706_);
                                            crate::leanh::lean_dec_ref(v_ctx_3684_);
                                            v_a_3775_ = crate::leanh::lean_ctor_get(v___x_3739_, 0);
                                            v_isSharedCheck_3782_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3739_))
                                                    as u8;
                                            if v_isSharedCheck_3782_ == 0 {
                                                v___x_3777_ = v___x_3739_;
                                                v_isShared_3778_ = v_isSharedCheck_3782_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3775_);
                                                crate::leanh::lean_dec(v___x_3739_);
                                                v___x_3777_ = crate::leanh::lean_box(0);
                                                v_isShared_3778_ = v_isSharedCheck_3782_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_3783_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3783_, 0, v_fst_3706_);
                                        crate::leanh::lean_ctor_set(v___x_3783_, 1, v_snd_3707_);
                                        v_a_3713_ = v___x_3783_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_3709_);
                                    crate::leanh::lean_dec(v_snd_3707_);
                                    crate::leanh::lean_dec(v_fst_3706_);
                                    crate::leanh::lean_dec_ref(v_ctx_3684_);
                                    v_a_3784_ = crate::leanh::lean_ctor_get(v___x_3735_, 0);
                                    v_isSharedCheck_3791_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3735_)) as u8;
                                    if v_isSharedCheck_3791_ == 0 {
                                        v___x_3786_ = v___x_3735_;
                                        v_isShared_3787_ = v_isSharedCheck_3791_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3784_);
                                        crate::leanh::lean_dec(v___x_3735_);
                                        v___x_3786_ = crate::leanh::lean_box(0);
                                        v_isShared_3787_ = v_isSharedCheck_3791_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3709_);
                            crate::leanh::lean_dec(v_snd_3707_);
                            crate::leanh::lean_dec(v_fst_3706_);
                            crate::leanh::lean_dec_ref(v_ctx_3684_);
                            v_a_3792_ = crate::leanh::lean_ctor_get(v___x_3730_, 0);
                            v_isSharedCheck_3799_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3730_)) as u8;
                            if v_isSharedCheck_3799_ == 0 {
                                v___x_3794_ = v___x_3730_;
                                v_isShared_3795_ = v_isSharedCheck_3799_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3792_);
                                crate::leanh::lean_dec(v___x_3730_);
                                v___x_3794_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_3760_, 1, v_fst_3758_);
                    crate::leanh::lean_ctor_set(v___x_3760_, 0, v_fst_3757_);
                    v___x_3763_ = v___x_3760_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3764_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_fst_3757_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_fst_3758_);
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
                    v_reuseFailAlloc_3773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
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
                    v_reuseFailAlloc_3781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
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
                    v_reuseFailAlloc_3790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
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
                    v_reuseFailAlloc_3798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
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
    mut v_ctx_3805_: *mut crate::leanh::LeanObject,
    mut v_as_3806_: *mut crate::leanh::LeanObject,
    mut v_sz_3807_: *mut crate::leanh::LeanObject,
    mut v_i_3808_: *mut crate::leanh::LeanObject,
    mut v_b_3809_: *mut crate::leanh::LeanObject,
    mut v___y_3810_: *mut crate::leanh::LeanObject,
    mut v___y_3811_: *mut crate::leanh::LeanObject,
    mut v___y_3812_: *mut crate::leanh::LeanObject,
    mut v___y_3813_: *mut crate::leanh::LeanObject,
    mut v___y_3814_: *mut crate::leanh::LeanObject,
    mut v___y_3815_: *mut crate::leanh::LeanObject,
    mut v___y_3816_: *mut crate::leanh::LeanObject,
    mut v___y_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3821_: usize = 0;
    let mut v_i_boxed_3822_: usize = 0;
    let mut v_res_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3821_ = crate::leanh::lean_unbox_usize(v_sz_3807_);
    crate::leanh::lean_dec(v_sz_3807_);
    v_i_boxed_3822_ = crate::leanh::lean_unbox_usize(v_i_3808_);
    crate::leanh::lean_dec(v_i_3808_);
    v_res_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_3805_, v_as_3806_, v_sz_boxed_3821_, v_i_boxed_3822_, v_b_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
    crate::leanh::lean_dec(v___y_3819_);
    crate::leanh::lean_dec_ref(v___y_3818_);
    crate::leanh::lean_dec(v___y_3817_);
    crate::leanh::lean_dec_ref(v___y_3816_);
    crate::leanh::lean_dec(v___y_3815_);
    crate::leanh::lean_dec_ref(v___y_3814_);
    crate::leanh::lean_dec(v___y_3813_);
    crate::leanh::lean_dec_ref(v___y_3812_);
    crate::leanh::lean_dec(v___y_3811_);
    crate::leanh::lean_dec(v___y_3810_);
    crate::leanh::lean_dec_ref(v_as_3806_);
    return v_res_3823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(
    mut v_ctx_3824_: *mut crate::leanh::LeanObject,
    mut v_as_3825_: *mut crate::leanh::LeanObject,
    mut v_sz_3826_: usize,
    mut v_i_3827_: usize,
    mut v_b_3828_: *mut crate::leanh::LeanObject,
    mut v___y_3829_: *mut crate::leanh::LeanObject,
    mut v___y_3830_: *mut crate::leanh::LeanObject,
    mut v___y_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
    mut v___y_3835_: *mut crate::leanh::LeanObject,
    mut v___y_3836_: *mut crate::leanh::LeanObject,
    mut v___y_3837_: *mut crate::leanh::LeanObject,
    mut v___y_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3840_: u8 = 0;
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3845_: u8 = 0;
    let mut v_fst_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: usize = 0;
    let mut v___x_3857_: usize = 0;
    let mut v_reuseFailAlloc_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: u8 = 0;
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: u8 = 0;
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInterpreted_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: u8 = 0;
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3882_: u8 = 0;
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3892_: usize = 0;
    let mut v___x_3893_: usize = 0;
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_unused_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3910_: u8 = 0;
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3914_: u8 = 0;
    let mut v_a_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3922_: u8 = 0;
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3927_: u8 = 0;
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v_a_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3935_: u8 = 0;
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3939_: u8 = 0;
    let mut v___x_3940_: u8 = 0;
    let mut v___x_3941_: u8 = 0;
    let mut v_isSharedCheck_3942_: u8 = 0;
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_unused_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3840_ = lean_usize_dec_lt(v_i_3827_, v_sz_3826_);
                if v___x_3840_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_3824_);
                    v___x_3841_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3841_, 0, v_b_3828_);
                    return v___x_3841_;
                } else {
                    v_snd_3842_ = crate::leanh::lean_ctor_get(v_b_3828_, 1);
                    v_isSharedCheck_3943_ = (!crate::leanh::lean_is_exclusive(v_b_3828_)) as u8;
                    if v_isSharedCheck_3943_ == 0 {
                        v_unused_3944_ = crate::leanh::lean_ctor_get(v_b_3828_, 0);
                        crate::leanh::lean_dec(v_unused_3944_);
                        v___x_3844_ = v_b_3828_;
                        v_isShared_3845_ = v_isSharedCheck_3943_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3842_);
                        crate::leanh::lean_dec(v_b_3828_);
                        v___x_3844_ = crate::leanh::lean_box(0);
                        v_isShared_3845_ = v_isSharedCheck_3943_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3846_ = crate::leanh::lean_ctor_get(v_snd_3842_, 0);
                v_snd_3847_ = crate::leanh::lean_ctor_get(v_snd_3842_, 1);
                v_isSharedCheck_3942_ = (!crate::leanh::lean_is_exclusive(v_snd_3842_)) as u8;
                if v_isSharedCheck_3942_ == 0 {
                    v___x_3849_ = v_snd_3842_;
                    v_isShared_3850_ = v_isSharedCheck_3942_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3847_);
                    crate::leanh::lean_inc(v_fst_3846_);
                    crate::leanh::lean_dec(v_snd_3842_);
                    v___x_3849_ = crate::leanh::lean_box(0);
                    v_isShared_3850_ = v_isSharedCheck_3942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3851_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_3849_, 1, v_a_3853_);
                    crate::leanh::lean_ctor_set(v___x_3849_, 0, v___x_3851_);
                    v___x_3855_ = v___x_3849_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3859_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 1, v_a_3853_);
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
                    crate::leanh::lean_ctor_set(v___x_3844_, 1, v_snd_3847_);
                    crate::leanh::lean_ctor_set(v___x_3844_, 0, v_fst_3846_);
                    v___x_3862_ = v___x_3844_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_fst_3846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_snd_3847_);
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
                v___x_3865_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3865_, 0, v_fst_3846_);
                crate::leanh::lean_ctor_set(v___x_3865_, 1, v_snd_3847_);
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
                        crate::leanh::lean_del_object(v___x_3844_);
                        crate::leanh::lean_inc(v_a_3866_);
                        v___x_3870_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                            v_a_3866_,
                            v___y_3829_,
                            v___y_3835_,
                            v___y_3836_,
                            v___y_3837_,
                            v___y_3838_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3870_) == 0 {
                            v_a_3871_ = crate::leanh::lean_ctor_get(v___x_3870_, 0);
                            crate::leanh::lean_inc(v_a_3871_);
                            crate::leanh::lean_dec_ref_known(v___x_3870_, 1);
                            v___x_3872_ = (crate::leanh::lean_unbox(v_a_3871_) as u8);
                            crate::leanh::lean_dec(v_a_3871_);
                            if v___x_3872_ == 0 {
                                v___x_3873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3873_, 0, v_fst_3846_);
                                crate::leanh::lean_ctor_set(v___x_3873_, 1, v_snd_3847_);
                                v_a_3853_ = v___x_3873_;
                                state = 3;
                                continue;
                            } else {
                                v_isInterpreted_3874_ = crate::leanh::lean_ctor_get(v_ctx_3824_, 0);
                                crate::leanh::lean_inc_ref(v_isInterpreted_3874_);
                                crate::leanh::lean_inc(v___y_3838_);
                                crate::leanh::lean_inc_ref(v___y_3837_);
                                crate::leanh::lean_inc(v___y_3836_);
                                crate::leanh::lean_inc_ref(v___y_3835_);
                                crate::leanh::lean_inc(v___y_3834_);
                                crate::leanh::lean_inc_ref(v___y_3833_);
                                crate::leanh::lean_inc(v___y_3832_);
                                crate::leanh::lean_inc_ref(v___y_3831_);
                                crate::leanh::lean_inc(v___y_3830_);
                                crate::leanh::lean_inc(v___y_3829_);
                                crate::leanh::lean_inc(v_a_3866_);
                                v___x_3875_ = crate::leanh::lean_apply_12(
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
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_3875_) == 0 {
                                    v_a_3876_ = crate::leanh::lean_ctor_get(v___x_3875_, 0);
                                    crate::leanh::lean_inc(v_a_3876_);
                                    crate::leanh::lean_dec_ref_known(v___x_3875_, 1);
                                    v___x_3877_ = (crate::leanh::lean_unbox(v_a_3876_) as u8);
                                    crate::leanh::lean_dec(v_a_3876_);
                                    if v___x_3877_ == 0 {
                                        v___x_3878_ = l_Lean_Expr_getAppFn(v_a_3866_);
                                        crate::leanh::lean_inc_ref(v___x_3878_);
                                        v___x_3879_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_3878_, v___y_3837_, v___y_3838_);
                                        if crate::leanh::lean_obj_tag(v___x_3879_) == 0 {
                                            v_a_3880_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                                            crate::leanh::lean_inc(v_a_3880_);
                                            crate::leanh::lean_dec_ref_known(v___x_3879_, 1);
                                            v___x_3881_ =
                                                (crate::leanh::lean_unbox(v_a_3880_) as u8);
                                            crate::leanh::lean_dec(v_a_3880_);
                                            if v___x_3881_ == 0 {
                                                v___x_3882_ =
                                                    l_Lean_Meta_Grind_isCastLikeFn(v___x_3878_);
                                                if v___x_3882_ == 0 {
                                                    v___x_3883_ =
                                                        crate::leanh::lean_unsigned_to_nat(0);
                                                    v_dummy_3884_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
                                                    v_nargs_3885_ =
                                                        l_Lean_Expr_getAppNumArgs(v_a_3866_);
                                                    crate::leanh::lean_inc(v_nargs_3885_);
                                                    v___x_3886_ =
                                                        lean_mk_array(v_nargs_3885_, v_dummy_3884_);
                                                    v___x_3887_ =
                                                        crate::leanh::lean_unsigned_to_nat(1);
                                                    v___x_3888_ =
                                                        lean_nat_sub(v_nargs_3885_, v___x_3887_);
                                                    crate::leanh::lean_dec(v_nargs_3885_);
                                                    crate::leanh::lean_inc_n(v_a_3866_, 2);
                                                    v___x_3889_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3866_, v___x_3886_, v___x_3888_);
                                                    v___x_3890_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3890_,
                                                        0,
                                                        v_snd_3847_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3890_,
                                                        1,
                                                        v___x_3883_,
                                                    );
                                                    v___x_3891_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3891_,
                                                        0,
                                                        v_fst_3846_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3891_,
                                                        1,
                                                        v___x_3890_,
                                                    );
                                                    v_sz_3892_ = lean_array_size(v___x_3889_);
                                                    v___x_3893_ = 0usize;
                                                    crate::leanh::lean_inc_ref(v_ctx_3824_);
                                                    v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_3866_, v_ctx_3824_, v___x_3878_, v___x_3889_, v_sz_3892_, v___x_3893_, v___x_3891_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
                                                    crate::leanh::lean_dec_ref(v___x_3889_);
                                                    if crate::leanh::lean_obj_tag(v___x_3894_) == 0
                                                    {
                                                        v_a_3895_ = crate::leanh::lean_ctor_get(
                                                            v___x_3894_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_3895_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3894_,
                                                            1,
                                                        );
                                                        v_snd_3896_ = crate::leanh::lean_ctor_get(
                                                            v_a_3895_, 1,
                                                        );
                                                        crate::leanh::lean_inc(v_snd_3896_);
                                                        v_fst_3897_ = crate::leanh::lean_ctor_get(
                                                            v_a_3895_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_fst_3897_);
                                                        crate::leanh::lean_dec(v_a_3895_);
                                                        v_fst_3898_ = crate::leanh::lean_ctor_get(
                                                            v_snd_3896_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3905_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v_snd_3896_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3905_ == 0 {
                                                            v_unused_3906_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_snd_3896_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_dec(v_unused_3906_);
                                                            v___x_3900_ = v_snd_3896_;
                                                            v_isShared_3901_ =
                                                                v_isSharedCheck_3905_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_fst_3898_);
                                                            crate::leanh::lean_dec(v_snd_3896_);
                                                            v___x_3900_ = crate::leanh::lean_box(0);
                                                            v_isShared_3901_ =
                                                                v_isSharedCheck_3905_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_del_object(v___x_3849_);
                                                        crate::leanh::lean_dec_ref(v_ctx_3824_);
                                                        v_a_3907_ = crate::leanh::lean_ctor_get(
                                                            v___x_3894_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3914_ =
                                                            (!crate::leanh::lean_is_exclusive(
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
                                                            crate::leanh::lean_inc(v_a_3907_);
                                                            crate::leanh::lean_dec(v___x_3894_);
                                                            v___x_3909_ = crate::leanh::lean_box(0);
                                                            v_isShared_3910_ =
                                                                v_isSharedCheck_3914_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_3878_);
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3878_);
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3878_);
                                            crate::leanh::lean_del_object(v___x_3849_);
                                            crate::leanh::lean_dec(v_snd_3847_);
                                            crate::leanh::lean_dec(v_fst_3846_);
                                            crate::leanh::lean_dec_ref(v_ctx_3824_);
                                            v_a_3915_ = crate::leanh::lean_ctor_get(v___x_3879_, 0);
                                            v_isSharedCheck_3922_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3879_))
                                                    as u8;
                                            if v_isSharedCheck_3922_ == 0 {
                                                v___x_3917_ = v___x_3879_;
                                                v_isShared_3918_ = v_isSharedCheck_3922_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3915_);
                                                crate::leanh::lean_dec(v___x_3879_);
                                                v___x_3917_ = crate::leanh::lean_box(0);
                                                v_isShared_3918_ = v_isSharedCheck_3922_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_3923_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3923_, 0, v_fst_3846_);
                                        crate::leanh::lean_ctor_set(v___x_3923_, 1, v_snd_3847_);
                                        v_a_3853_ = v___x_3923_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_3849_);
                                    crate::leanh::lean_dec(v_snd_3847_);
                                    crate::leanh::lean_dec(v_fst_3846_);
                                    crate::leanh::lean_dec_ref(v_ctx_3824_);
                                    v_a_3924_ = crate::leanh::lean_ctor_get(v___x_3875_, 0);
                                    v_isSharedCheck_3931_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3875_)) as u8;
                                    if v_isSharedCheck_3931_ == 0 {
                                        v___x_3926_ = v___x_3875_;
                                        v_isShared_3927_ = v_isSharedCheck_3931_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3924_);
                                        crate::leanh::lean_dec(v___x_3875_);
                                        v___x_3926_ = crate::leanh::lean_box(0);
                                        v_isShared_3927_ = v_isSharedCheck_3931_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3849_);
                            crate::leanh::lean_dec(v_snd_3847_);
                            crate::leanh::lean_dec(v_fst_3846_);
                            crate::leanh::lean_dec_ref(v_ctx_3824_);
                            v_a_3932_ = crate::leanh::lean_ctor_get(v___x_3870_, 0);
                            v_isSharedCheck_3939_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3870_)) as u8;
                            if v_isSharedCheck_3939_ == 0 {
                                v___x_3934_ = v___x_3870_;
                                v_isShared_3935_ = v_isSharedCheck_3939_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3932_);
                                crate::leanh::lean_dec(v___x_3870_);
                                v___x_3934_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_3900_, 1, v_fst_3898_);
                    crate::leanh::lean_ctor_set(v___x_3900_, 0, v_fst_3897_);
                    v___x_3903_ = v___x_3900_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_fst_3897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_fst_3898_);
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
                    v_reuseFailAlloc_3913_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
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
                    v_reuseFailAlloc_3921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
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
                    v_reuseFailAlloc_3930_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
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
                    v_reuseFailAlloc_3938_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
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
    mut v_ctx_3945_: *mut crate::leanh::LeanObject,
    mut v_as_3946_: *mut crate::leanh::LeanObject,
    mut v_sz_3947_: *mut crate::leanh::LeanObject,
    mut v_i_3948_: *mut crate::leanh::LeanObject,
    mut v_b_3949_: *mut crate::leanh::LeanObject,
    mut v___y_3950_: *mut crate::leanh::LeanObject,
    mut v___y_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
    mut v___y_3957_: *mut crate::leanh::LeanObject,
    mut v___y_3958_: *mut crate::leanh::LeanObject,
    mut v___y_3959_: *mut crate::leanh::LeanObject,
    mut v___y_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3961_: usize = 0;
    let mut v_i_boxed_3962_: usize = 0;
    let mut v_res_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3961_ = crate::leanh::lean_unbox_usize(v_sz_3947_);
    crate::leanh::lean_dec(v_sz_3947_);
    v_i_boxed_3962_ = crate::leanh::lean_unbox_usize(v_i_3948_);
    crate::leanh::lean_dec(v_i_3948_);
    v_res_3963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18_spec__26(v_ctx_3945_, v_as_3946_, v_sz_boxed_3961_, v_i_boxed_3962_, v_b_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
    crate::leanh::lean_dec(v___y_3959_);
    crate::leanh::lean_dec_ref(v___y_3958_);
    crate::leanh::lean_dec(v___y_3957_);
    crate::leanh::lean_dec_ref(v___y_3956_);
    crate::leanh::lean_dec(v___y_3955_);
    crate::leanh::lean_dec_ref(v___y_3954_);
    crate::leanh::lean_dec(v___y_3953_);
    crate::leanh::lean_dec_ref(v___y_3952_);
    crate::leanh::lean_dec(v___y_3951_);
    crate::leanh::lean_dec(v___y_3950_);
    crate::leanh::lean_dec_ref(v_as_3946_);
    return v_res_3963_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(
    mut v_ctx_3964_: *mut crate::leanh::LeanObject,
    mut v_as_3965_: *mut crate::leanh::LeanObject,
    mut v_sz_3966_: usize,
    mut v_i_3967_: usize,
    mut v_b_3968_: *mut crate::leanh::LeanObject,
    mut v___y_3969_: *mut crate::leanh::LeanObject,
    mut v___y_3970_: *mut crate::leanh::LeanObject,
    mut v___y_3971_: *mut crate::leanh::LeanObject,
    mut v___y_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3980_: u8 = 0;
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3985_: u8 = 0;
    let mut v_fst_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: usize = 0;
    let mut v___x_3997_: usize = 0;
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4008_: u8 = 0;
    let mut v___x_4009_: u8 = 0;
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: u8 = 0;
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInterpreted_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4032_: usize = 0;
    let mut v___x_4033_: usize = 0;
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut v_unused_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4050_: u8 = 0;
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4054_: u8 = 0;
    let mut v_a_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4058_: u8 = 0;
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4062_: u8 = 0;
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4067_: u8 = 0;
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut v_a_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4075_: u8 = 0;
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4079_: u8 = 0;
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: u8 = 0;
    let mut v_isSharedCheck_4082_: u8 = 0;
    let mut v_isSharedCheck_4083_: u8 = 0;
    let mut v_unused_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3980_ = lean_usize_dec_lt(v_i_3967_, v_sz_3966_);
                if v___x_3980_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_3964_);
                    v___x_3981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3981_, 0, v_b_3968_);
                    return v___x_3981_;
                } else {
                    v_snd_3982_ = crate::leanh::lean_ctor_get(v_b_3968_, 1);
                    v_isSharedCheck_4083_ = (!crate::leanh::lean_is_exclusive(v_b_3968_)) as u8;
                    if v_isSharedCheck_4083_ == 0 {
                        v_unused_4084_ = crate::leanh::lean_ctor_get(v_b_3968_, 0);
                        crate::leanh::lean_dec(v_unused_4084_);
                        v___x_3984_ = v_b_3968_;
                        v_isShared_3985_ = v_isSharedCheck_4083_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3982_);
                        crate::leanh::lean_dec(v_b_3968_);
                        v___x_3984_ = crate::leanh::lean_box(0);
                        v_isShared_3985_ = v_isSharedCheck_4083_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3986_ = crate::leanh::lean_ctor_get(v_snd_3982_, 0);
                v_snd_3987_ = crate::leanh::lean_ctor_get(v_snd_3982_, 1);
                v_isSharedCheck_4082_ = (!crate::leanh::lean_is_exclusive(v_snd_3982_)) as u8;
                if v_isSharedCheck_4082_ == 0 {
                    v___x_3989_ = v_snd_3982_;
                    v_isShared_3990_ = v_isSharedCheck_4082_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3987_);
                    crate::leanh::lean_inc(v_fst_3986_);
                    crate::leanh::lean_dec(v_snd_3982_);
                    v___x_3989_ = crate::leanh::lean_box(0);
                    v_isShared_3990_ = v_isSharedCheck_4082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3991_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_3989_, 1, v_a_3993_);
                    crate::leanh::lean_ctor_set(v___x_3989_, 0, v___x_3991_);
                    v___x_3995_ = v___x_3989_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3999_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_a_3993_);
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
                    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_snd_3987_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v_fst_3986_);
                    v___x_4002_ = v___x_3984_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4003_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_fst_3986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_snd_3987_);
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
                v___x_4005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4005_, 0, v_fst_3986_);
                crate::leanh::lean_ctor_set(v___x_4005_, 1, v_snd_3987_);
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
                        crate::leanh::lean_del_object(v___x_3984_);
                        crate::leanh::lean_inc(v_a_4006_);
                        v___x_4010_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                            v_a_4006_,
                            v___y_3969_,
                            v___y_3975_,
                            v___y_3976_,
                            v___y_3977_,
                            v___y_3978_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4010_) == 0 {
                            v_a_4011_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                            crate::leanh::lean_inc(v_a_4011_);
                            crate::leanh::lean_dec_ref_known(v___x_4010_, 1);
                            v___x_4012_ = (crate::leanh::lean_unbox(v_a_4011_) as u8);
                            crate::leanh::lean_dec(v_a_4011_);
                            if v___x_4012_ == 0 {
                                v___x_4013_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4013_, 0, v_fst_3986_);
                                crate::leanh::lean_ctor_set(v___x_4013_, 1, v_snd_3987_);
                                v_a_3993_ = v___x_4013_;
                                state = 3;
                                continue;
                            } else {
                                v_isInterpreted_4014_ = crate::leanh::lean_ctor_get(v_ctx_3964_, 0);
                                crate::leanh::lean_inc_ref(v_isInterpreted_4014_);
                                crate::leanh::lean_inc(v___y_3978_);
                                crate::leanh::lean_inc_ref(v___y_3977_);
                                crate::leanh::lean_inc(v___y_3976_);
                                crate::leanh::lean_inc_ref(v___y_3975_);
                                crate::leanh::lean_inc(v___y_3974_);
                                crate::leanh::lean_inc_ref(v___y_3973_);
                                crate::leanh::lean_inc(v___y_3972_);
                                crate::leanh::lean_inc_ref(v___y_3971_);
                                crate::leanh::lean_inc(v___y_3970_);
                                crate::leanh::lean_inc(v___y_3969_);
                                crate::leanh::lean_inc(v_a_4006_);
                                v___x_4015_ = crate::leanh::lean_apply_12(
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
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_4015_) == 0 {
                                    v_a_4016_ = crate::leanh::lean_ctor_get(v___x_4015_, 0);
                                    crate::leanh::lean_inc(v_a_4016_);
                                    crate::leanh::lean_dec_ref_known(v___x_4015_, 1);
                                    v___x_4017_ = (crate::leanh::lean_unbox(v_a_4016_) as u8);
                                    crate::leanh::lean_dec(v_a_4016_);
                                    if v___x_4017_ == 0 {
                                        v___x_4018_ = l_Lean_Expr_getAppFn(v_a_4006_);
                                        crate::leanh::lean_inc_ref(v___x_4018_);
                                        v___x_4019_ = l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_isFnInstance(v___x_4018_, v___y_3977_, v___y_3978_);
                                        if crate::leanh::lean_obj_tag(v___x_4019_) == 0 {
                                            v_a_4020_ = crate::leanh::lean_ctor_get(v___x_4019_, 0);
                                            crate::leanh::lean_inc(v_a_4020_);
                                            crate::leanh::lean_dec_ref_known(v___x_4019_, 1);
                                            v___x_4021_ =
                                                (crate::leanh::lean_unbox(v_a_4020_) as u8);
                                            crate::leanh::lean_dec(v_a_4020_);
                                            if v___x_4021_ == 0 {
                                                v___x_4022_ =
                                                    l_Lean_Meta_Grind_isCastLikeFn(v___x_4018_);
                                                if v___x_4022_ == 0 {
                                                    v___x_4023_ =
                                                        crate::leanh::lean_unsigned_to_nat(0);
                                                    v_dummy_4024_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mkKey___closed__0);
                                                    v_nargs_4025_ =
                                                        l_Lean_Expr_getAppNumArgs(v_a_4006_);
                                                    crate::leanh::lean_inc(v_nargs_4025_);
                                                    v___x_4026_ =
                                                        lean_mk_array(v_nargs_4025_, v_dummy_4024_);
                                                    v___x_4027_ =
                                                        crate::leanh::lean_unsigned_to_nat(1);
                                                    v___x_4028_ =
                                                        lean_nat_sub(v_nargs_4025_, v___x_4027_);
                                                    crate::leanh::lean_dec(v_nargs_4025_);
                                                    crate::leanh::lean_inc_n(v_a_4006_, 2);
                                                    v___x_4029_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4006_, v___x_4026_, v___x_4028_);
                                                    v___x_4030_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_4030_,
                                                        0,
                                                        v_snd_3987_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_4030_,
                                                        1,
                                                        v___x_4023_,
                                                    );
                                                    v___x_4031_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_4031_,
                                                        0,
                                                        v_fst_3986_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_4031_,
                                                        1,
                                                        v___x_4030_,
                                                    );
                                                    v_sz_4032_ = lean_array_size(v___x_4029_);
                                                    v___x_4033_ = 0usize;
                                                    crate::leanh::lean_inc_ref(v_ctx_3964_);
                                                    v___x_4034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6(v_a_4006_, v_ctx_3964_, v___x_4018_, v___x_4029_, v_sz_4032_, v___x_4033_, v___x_4031_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
                                                    crate::leanh::lean_dec_ref(v___x_4029_);
                                                    if crate::leanh::lean_obj_tag(v___x_4034_) == 0
                                                    {
                                                        v_a_4035_ = crate::leanh::lean_ctor_get(
                                                            v___x_4034_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_4035_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_4034_,
                                                            1,
                                                        );
                                                        v_snd_4036_ = crate::leanh::lean_ctor_get(
                                                            v_a_4035_, 1,
                                                        );
                                                        crate::leanh::lean_inc(v_snd_4036_);
                                                        v_fst_4037_ = crate::leanh::lean_ctor_get(
                                                            v_a_4035_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_fst_4037_);
                                                        crate::leanh::lean_dec(v_a_4035_);
                                                        v_fst_4038_ = crate::leanh::lean_ctor_get(
                                                            v_snd_4036_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4045_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v_snd_4036_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_4045_ == 0 {
                                                            v_unused_4046_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_snd_4036_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_dec(v_unused_4046_);
                                                            v___x_4040_ = v_snd_4036_;
                                                            v_isShared_4041_ =
                                                                v_isSharedCheck_4045_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_fst_4038_);
                                                            crate::leanh::lean_dec(v_snd_4036_);
                                                            v___x_4040_ = crate::leanh::lean_box(0);
                                                            v_isShared_4041_ =
                                                                v_isSharedCheck_4045_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_del_object(v___x_3989_);
                                                        crate::leanh::lean_dec_ref(v_ctx_3964_);
                                                        v_a_4047_ = crate::leanh::lean_ctor_get(
                                                            v___x_4034_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_4054_ =
                                                            (!crate::leanh::lean_is_exclusive(
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
                                                            crate::leanh::lean_inc(v_a_4047_);
                                                            crate::leanh::lean_dec(v___x_4034_);
                                                            v___x_4049_ = crate::leanh::lean_box(0);
                                                            v_isShared_4050_ =
                                                                v_isSharedCheck_4054_;
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_4018_);
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_4018_);
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_4018_);
                                            crate::leanh::lean_del_object(v___x_3989_);
                                            crate::leanh::lean_dec(v_snd_3987_);
                                            crate::leanh::lean_dec(v_fst_3986_);
                                            crate::leanh::lean_dec_ref(v_ctx_3964_);
                                            v_a_4055_ = crate::leanh::lean_ctor_get(v___x_4019_, 0);
                                            v_isSharedCheck_4062_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4019_))
                                                    as u8;
                                            if v_isSharedCheck_4062_ == 0 {
                                                v___x_4057_ = v___x_4019_;
                                                v_isShared_4058_ = v_isSharedCheck_4062_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4055_);
                                                crate::leanh::lean_dec(v___x_4019_);
                                                v___x_4057_ = crate::leanh::lean_box(0);
                                                v_isShared_4058_ = v_isSharedCheck_4062_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_4063_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4063_, 0, v_fst_3986_);
                                        crate::leanh::lean_ctor_set(v___x_4063_, 1, v_snd_3987_);
                                        v_a_3993_ = v___x_4063_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_3989_);
                                    crate::leanh::lean_dec(v_snd_3987_);
                                    crate::leanh::lean_dec(v_fst_3986_);
                                    crate::leanh::lean_dec_ref(v_ctx_3964_);
                                    v_a_4064_ = crate::leanh::lean_ctor_get(v___x_4015_, 0);
                                    v_isSharedCheck_4071_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4015_)) as u8;
                                    if v_isSharedCheck_4071_ == 0 {
                                        v___x_4066_ = v___x_4015_;
                                        v_isShared_4067_ = v_isSharedCheck_4071_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4064_);
                                        crate::leanh::lean_dec(v___x_4015_);
                                        v___x_4066_ = crate::leanh::lean_box(0);
                                        v_isShared_4067_ = v_isSharedCheck_4071_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3989_);
                            crate::leanh::lean_dec(v_snd_3987_);
                            crate::leanh::lean_dec(v_fst_3986_);
                            crate::leanh::lean_dec_ref(v_ctx_3964_);
                            v_a_4072_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                            v_isSharedCheck_4079_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4010_)) as u8;
                            if v_isSharedCheck_4079_ == 0 {
                                v___x_4074_ = v___x_4010_;
                                v_isShared_4075_ = v_isSharedCheck_4079_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4072_);
                                crate::leanh::lean_dec(v___x_4010_);
                                v___x_4074_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_4040_, 1, v_fst_4038_);
                    crate::leanh::lean_ctor_set(v___x_4040_, 0, v_fst_4037_);
                    v___x_4043_ = v___x_4040_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_fst_4037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_fst_4038_);
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
                    v_reuseFailAlloc_4053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
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
                    v_reuseFailAlloc_4061_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
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
                    v_reuseFailAlloc_4070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
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
                    v_reuseFailAlloc_4078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
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
    mut v_ctx_4085_: *mut crate::leanh::LeanObject,
    mut v_as_4086_: *mut crate::leanh::LeanObject,
    mut v_sz_4087_: *mut crate::leanh::LeanObject,
    mut v_i_4088_: *mut crate::leanh::LeanObject,
    mut v_b_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
    mut v___y_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
    mut v___y_4098_: *mut crate::leanh::LeanObject,
    mut v___y_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4101_: usize = 0;
    let mut v_i_boxed_4102_: usize = 0;
    let mut v_res_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4101_ = crate::leanh::lean_unbox_usize(v_sz_4087_);
    crate::leanh::lean_dec(v_sz_4087_);
    v_i_boxed_4102_ = crate::leanh::lean_unbox_usize(v_i_4088_);
    crate::leanh::lean_dec(v_i_4088_);
    v_res_4103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_4085_, v_as_4086_, v_sz_boxed_4101_, v_i_boxed_4102_, v_b_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
    crate::leanh::lean_dec(v___y_4099_);
    crate::leanh::lean_dec_ref(v___y_4098_);
    crate::leanh::lean_dec(v___y_4097_);
    crate::leanh::lean_dec_ref(v___y_4096_);
    crate::leanh::lean_dec(v___y_4095_);
    crate::leanh::lean_dec_ref(v___y_4094_);
    crate::leanh::lean_dec(v___y_4093_);
    crate::leanh::lean_dec_ref(v___y_4092_);
    crate::leanh::lean_dec(v___y_4091_);
    crate::leanh::lean_dec(v___y_4090_);
    crate::leanh::lean_dec_ref(v_as_4086_);
    return v_res_4103_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(
    mut v_init_4104_: *mut crate::leanh::LeanObject,
    mut v_ctx_4105_: *mut crate::leanh::LeanObject,
    mut v_n_4106_: *mut crate::leanh::LeanObject,
    mut v_b_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4122_: usize = 0;
    let mut v___x_4123_: usize = 0;
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4128_: u8 = 0;
    let mut v_fst_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut v_a_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4143_: u8 = 0;
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_vs_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4151_: usize = 0;
    let mut v___x_4152_: usize = 0;
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4157_: u8 = 0;
    let mut v_fst_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v_a_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4172_: u8 = 0;
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_4106_) == 0 {
                    v_cs_4119_ = crate::leanh::lean_ctor_get(v_n_4106_, 0);
                    v___x_4120_ = crate::leanh::lean_box(0);
                    v___x_4121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4121_, 0, v___x_4120_);
                    crate::leanh::lean_ctor_set(v___x_4121_, 1, v_b_4107_);
                    v_sz_4122_ = lean_array_size(v_cs_4119_);
                    v___x_4123_ = 0usize;
                    v___x_4124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_4104_, v_ctx_4105_, v_cs_4119_, v_sz_4122_, v___x_4123_, v___x_4121_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
                    if crate::leanh::lean_obj_tag(v___x_4124_) == 0 {
                        v_a_4125_ = crate::leanh::lean_ctor_get(v___x_4124_, 0);
                        v_isSharedCheck_4139_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4124_)) as u8;
                        if v_isSharedCheck_4139_ == 0 {
                            v___x_4127_ = v___x_4124_;
                            v_isShared_4128_ = v_isSharedCheck_4139_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4125_);
                            crate::leanh::lean_dec(v___x_4124_);
                            v___x_4127_ = crate::leanh::lean_box(0);
                            v_isShared_4128_ = v_isSharedCheck_4139_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4140_ = crate::leanh::lean_ctor_get(v___x_4124_, 0);
                        v_isSharedCheck_4147_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4124_)) as u8;
                        if v_isSharedCheck_4147_ == 0 {
                            v___x_4142_ = v___x_4124_;
                            v_isShared_4143_ = v_isSharedCheck_4147_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4140_);
                            crate::leanh::lean_dec(v___x_4124_);
                            v___x_4142_ = crate::leanh::lean_box(0);
                            v_isShared_4143_ = v_isSharedCheck_4147_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4148_ = crate::leanh::lean_ctor_get(v_n_4106_, 0);
                    v___x_4149_ = crate::leanh::lean_box(0);
                    v___x_4150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4150_, 0, v___x_4149_);
                    crate::leanh::lean_ctor_set(v___x_4150_, 1, v_b_4107_);
                    v_sz_4151_ = lean_array_size(v_vs_4148_);
                    v___x_4152_ = 0usize;
                    v___x_4153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__18(v_ctx_4105_, v_vs_4148_, v_sz_4151_, v___x_4152_, v___x_4150_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
                    if crate::leanh::lean_obj_tag(v___x_4153_) == 0 {
                        v_a_4154_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                        v_isSharedCheck_4168_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4153_)) as u8;
                        if v_isSharedCheck_4168_ == 0 {
                            v___x_4156_ = v___x_4153_;
                            v_isShared_4157_ = v_isSharedCheck_4168_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4154_);
                            crate::leanh::lean_dec(v___x_4153_);
                            v___x_4156_ = crate::leanh::lean_box(0);
                            v_isShared_4157_ = v_isSharedCheck_4168_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4169_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                        v_isSharedCheck_4176_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4153_)) as u8;
                        if v_isSharedCheck_4176_ == 0 {
                            v___x_4171_ = v___x_4153_;
                            v_isShared_4172_ = v_isSharedCheck_4176_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4169_);
                            crate::leanh::lean_dec(v___x_4153_);
                            v___x_4171_ = crate::leanh::lean_box(0);
                            v_isShared_4172_ = v_isSharedCheck_4176_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4129_ = crate::leanh::lean_ctor_get(v_a_4125_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4129_) == 0 {
                    v_snd_4130_ = crate::leanh::lean_ctor_get(v_a_4125_, 1);
                    crate::leanh::lean_inc(v_snd_4130_);
                    crate::leanh::lean_dec(v_a_4125_);
                    v___x_4131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4131_, 0, v_snd_4130_);
                    if v_isShared_4128_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4127_, 0, v___x_4131_);
                        v___x_4133_ = v___x_4127_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
                        v___x_4133_ = v_reuseFailAlloc_4134_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4129_);
                    crate::leanh::lean_dec(v_a_4125_);
                    v_val_4135_ = crate::leanh::lean_ctor_get(v_fst_4129_, 0);
                    crate::leanh::lean_inc(v_val_4135_);
                    crate::leanh::lean_dec_ref_known(v_fst_4129_, 1);
                    if v_isShared_4128_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4127_, 0, v_val_4135_);
                        v___x_4137_ = v___x_4127_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4138_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_val_4135_);
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
                    v_reuseFailAlloc_4146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
                    v___x_4145_ = v_reuseFailAlloc_4146_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4145_;
            }
            6 => {
                v_fst_4158_ = crate::leanh::lean_ctor_get(v_a_4154_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4158_) == 0 {
                    v_snd_4159_ = crate::leanh::lean_ctor_get(v_a_4154_, 1);
                    crate::leanh::lean_inc(v_snd_4159_);
                    crate::leanh::lean_dec(v_a_4154_);
                    v___x_4160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4160_, 0, v_snd_4159_);
                    if v_isShared_4157_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4156_, 0, v___x_4160_);
                        v___x_4162_ = v___x_4156_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4160_);
                        v___x_4162_ = v_reuseFailAlloc_4163_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4158_);
                    crate::leanh::lean_dec(v_a_4154_);
                    v_val_4164_ = crate::leanh::lean_ctor_get(v_fst_4158_, 0);
                    crate::leanh::lean_inc(v_val_4164_);
                    crate::leanh::lean_dec_ref_known(v_fst_4158_, 1);
                    if v_isShared_4157_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4156_, 0, v_val_4164_);
                        v___x_4166_ = v___x_4156_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_val_4164_);
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
                    v_reuseFailAlloc_4175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
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
    mut v_init_4177_: *mut crate::leanh::LeanObject,
    mut v_ctx_4178_: *mut crate::leanh::LeanObject,
    mut v_as_4179_: *mut crate::leanh::LeanObject,
    mut v_sz_4180_: usize,
    mut v_i_4181_: usize,
    mut v_b_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4194_: u8 = 0;
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v_a_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4205_: u8 = 0;
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: usize = 0;
    let mut v___x_4218_: usize = 0;
    let mut v_reuseFailAlloc_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v_a_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4225_: u8 = 0;
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v_unused_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4194_ = lean_usize_dec_lt(v_i_4181_, v_sz_4180_);
                if v___x_4194_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_4178_);
                    v___x_4195_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4195_, 0, v_b_4182_);
                    return v___x_4195_;
                } else {
                    v_snd_4196_ = crate::leanh::lean_ctor_get(v_b_4182_, 1);
                    v_isSharedCheck_4230_ = (!crate::leanh::lean_is_exclusive(v_b_4182_)) as u8;
                    if v_isSharedCheck_4230_ == 0 {
                        v_unused_4231_ = crate::leanh::lean_ctor_get(v_b_4182_, 0);
                        crate::leanh::lean_dec(v_unused_4231_);
                        v___x_4198_ = v_b_4182_;
                        v_isShared_4199_ = v_isSharedCheck_4230_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4196_);
                        crate::leanh::lean_dec(v_b_4182_);
                        v___x_4198_ = crate::leanh::lean_box(0);
                        v_isShared_4199_ = v_isSharedCheck_4230_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4200_ = lean_array_uget_borrowed(v_as_4179_, v_i_4181_);
                crate::leanh::lean_inc(v_snd_4196_);
                crate::leanh::lean_inc_ref(v_ctx_4178_);
                v___x_4201_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_4177_, v_ctx_4178_, v_a_4200_, v_snd_4196_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
                if crate::leanh::lean_obj_tag(v___x_4201_) == 0 {
                    v_a_4202_ = crate::leanh::lean_ctor_get(v___x_4201_, 0);
                    v_isSharedCheck_4221_ = (!crate::leanh::lean_is_exclusive(v___x_4201_)) as u8;
                    if v_isSharedCheck_4221_ == 0 {
                        v___x_4204_ = v___x_4201_;
                        v_isShared_4205_ = v_isSharedCheck_4221_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4202_);
                        crate::leanh::lean_dec(v___x_4201_);
                        v___x_4204_ = crate::leanh::lean_box(0);
                        v_isShared_4205_ = v_isSharedCheck_4221_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4198_);
                    crate::leanh::lean_dec(v_snd_4196_);
                    crate::leanh::lean_dec_ref(v_ctx_4178_);
                    v_a_4222_ = crate::leanh::lean_ctor_get(v___x_4201_, 0);
                    v_isSharedCheck_4229_ = (!crate::leanh::lean_is_exclusive(v___x_4201_)) as u8;
                    if v_isSharedCheck_4229_ == 0 {
                        v___x_4224_ = v___x_4201_;
                        v_isShared_4225_ = v_isSharedCheck_4229_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4222_);
                        crate::leanh::lean_dec(v___x_4201_);
                        v___x_4224_ = crate::leanh::lean_box(0);
                        v_isShared_4225_ = v_isSharedCheck_4229_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4202_) == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_4178_);
                    v___x_4206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4206_, 0, v_a_4202_);
                    if v_isShared_4199_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4198_, 0, v___x_4206_);
                        v___x_4208_ = v___x_4198_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4212_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4206_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 1, v_snd_4196_);
                        v___x_4208_ = v_reuseFailAlloc_4212_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4204_);
                    crate::leanh::lean_dec(v_snd_4196_);
                    v_a_4213_ = crate::leanh::lean_ctor_get(v_a_4202_, 0);
                    crate::leanh::lean_inc(v_a_4213_);
                    crate::leanh::lean_dec_ref_known(v_a_4202_, 1);
                    v___x_4214_ = crate::leanh::lean_box(0);
                    if v_isShared_4199_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4198_, 1, v_a_4213_);
                        crate::leanh::lean_ctor_set(v___x_4198_, 0, v___x_4214_);
                        v___x_4216_ = v___x_4198_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4214_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_a_4213_);
                        v___x_4216_ = v_reuseFailAlloc_4220_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4205_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4204_, 0, v___x_4208_);
                    v___x_4210_ = v___x_4204_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
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
                    v_reuseFailAlloc_4228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_4232_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_ctx_4233_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_4234_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_sz_4235_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_i_4236_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_4237_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4238_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4239_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4240_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4241_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4242_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4243_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4244_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4245_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4246_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4247_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4248_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_4249_: usize = 0;
    let mut v_i_boxed_4250_: usize = 0;
    let mut v_res_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4249_ = crate::leanh::lean_unbox_usize(v_sz_4235_);
    crate::leanh::lean_dec(v_sz_4235_);
    v_i_boxed_4250_ = crate::leanh::lean_unbox_usize(v_i_4236_);
    crate::leanh::lean_dec(v_i_4236_);
    v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14_spec__17(v_init_4232_, v_ctx_4233_, v_as_4234_, v_sz_boxed_4249_, v_i_boxed_4250_, v_b_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
    crate::leanh::lean_dec(v___y_4247_);
    crate::leanh::lean_dec_ref(v___y_4246_);
    crate::leanh::lean_dec(v___y_4245_);
    crate::leanh::lean_dec_ref(v___y_4244_);
    crate::leanh::lean_dec(v___y_4243_);
    crate::leanh::lean_dec_ref(v___y_4242_);
    crate::leanh::lean_dec(v___y_4241_);
    crate::leanh::lean_dec_ref(v___y_4240_);
    crate::leanh::lean_dec(v___y_4239_);
    crate::leanh::lean_dec(v___y_4238_);
    crate::leanh::lean_dec_ref(v_as_4234_);
    crate::leanh::lean_dec_ref(v_init_4232_);
    return v_res_4251_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14___boxed(
    mut v_init_4252_: *mut crate::leanh::LeanObject,
    mut v_ctx_4253_: *mut crate::leanh::LeanObject,
    mut v_n_4254_: *mut crate::leanh::LeanObject,
    mut v_b_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
    mut v___y_4259_: *mut crate::leanh::LeanObject,
    mut v___y_4260_: *mut crate::leanh::LeanObject,
    mut v___y_4261_: *mut crate::leanh::LeanObject,
    mut v___y_4262_: *mut crate::leanh::LeanObject,
    mut v___y_4263_: *mut crate::leanh::LeanObject,
    mut v___y_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
    mut v___y_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4267_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_4252_, v_ctx_4253_, v_n_4254_, v_b_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
    crate::leanh::lean_dec(v___y_4265_);
    crate::leanh::lean_dec_ref(v___y_4264_);
    crate::leanh::lean_dec(v___y_4263_);
    crate::leanh::lean_dec_ref(v___y_4262_);
    crate::leanh::lean_dec(v___y_4261_);
    crate::leanh::lean_dec_ref(v___y_4260_);
    crate::leanh::lean_dec(v___y_4259_);
    crate::leanh::lean_dec_ref(v___y_4258_);
    crate::leanh::lean_dec(v___y_4257_);
    crate::leanh::lean_dec(v___y_4256_);
    crate::leanh::lean_dec_ref(v_n_4254_);
    crate::leanh::lean_dec_ref(v_init_4252_);
    return v_res_4267_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7(
    mut v_ctx_4268_: *mut crate::leanh::LeanObject,
    mut v_t_4269_: *mut crate::leanh::LeanObject,
    mut v_init_4270_: *mut crate::leanh::LeanObject,
    mut v___y_4271_: *mut crate::leanh::LeanObject,
    mut v___y_4272_: *mut crate::leanh::LeanObject,
    mut v___y_4273_: *mut crate::leanh::LeanObject,
    mut v___y_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
    mut v___y_4277_: *mut crate::leanh::LeanObject,
    mut v___y_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
    mut v___y_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v_a_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4296_: usize = 0;
    let mut v___x_4297_: usize = 0;
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4302_: u8 = 0;
    let mut v_fst_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4312_: u8 = 0;
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_isSharedCheck_4321_: u8 = 0;
    let mut v_a_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4282_ = crate::leanh::lean_ctor_get(v_t_4269_, 0);
                v_tail_4283_ = crate::leanh::lean_ctor_get(v_t_4269_, 1);
                crate::leanh::lean_inc_ref(v_ctx_4268_);
                crate::leanh::lean_inc_ref(v_init_4270_);
                v___x_4284_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__14(v_init_4270_, v_ctx_4268_, v_root_4282_, v_init_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
                crate::leanh::lean_dec_ref(v_init_4270_);
                if crate::leanh::lean_obj_tag(v___x_4284_) == 0 {
                    v_a_4285_ = crate::leanh::lean_ctor_get(v___x_4284_, 0);
                    v_isSharedCheck_4321_ = (!crate::leanh::lean_is_exclusive(v___x_4284_)) as u8;
                    if v_isSharedCheck_4321_ == 0 {
                        v___x_4287_ = v___x_4284_;
                        v_isShared_4288_ = v_isSharedCheck_4321_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4285_);
                        crate::leanh::lean_dec(v___x_4284_);
                        v___x_4287_ = crate::leanh::lean_box(0);
                        v_isShared_4288_ = v_isSharedCheck_4321_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ctx_4268_);
                    v_a_4322_ = crate::leanh::lean_ctor_get(v___x_4284_, 0);
                    v_isSharedCheck_4329_ = (!crate::leanh::lean_is_exclusive(v___x_4284_)) as u8;
                    if v_isSharedCheck_4329_ == 0 {
                        v___x_4324_ = v___x_4284_;
                        v_isShared_4325_ = v_isSharedCheck_4329_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4322_);
                        crate::leanh::lean_dec(v___x_4284_);
                        v___x_4324_ = crate::leanh::lean_box(0);
                        v_isShared_4325_ = v_isSharedCheck_4329_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4285_) == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_4268_);
                    v_a_4289_ = crate::leanh::lean_ctor_get(v_a_4285_, 0);
                    crate::leanh::lean_inc(v_a_4289_);
                    crate::leanh::lean_dec_ref_known(v_a_4285_, 1);
                    if v_isShared_4288_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4287_, 0, v_a_4289_);
                        v___x_4291_ = v___x_4287_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4292_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4289_);
                        v___x_4291_ = v_reuseFailAlloc_4292_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4287_);
                    v_a_4293_ = crate::leanh::lean_ctor_get(v_a_4285_, 0);
                    crate::leanh::lean_inc(v_a_4293_);
                    crate::leanh::lean_dec_ref_known(v_a_4285_, 1);
                    v___x_4294_ = crate::leanh::lean_box(0);
                    v___x_4295_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4295_, 0, v___x_4294_);
                    crate::leanh::lean_ctor_set(v___x_4295_, 1, v_a_4293_);
                    v_sz_4296_ = lean_array_size(v_tail_4283_);
                    v___x_4297_ = 0usize;
                    v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_mbtc_spec__7_spec__15(v_ctx_4268_, v_tail_4283_, v_sz_4296_, v___x_4297_, v___x_4295_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
                    if crate::leanh::lean_obj_tag(v___x_4298_) == 0 {
                        v_a_4299_ = crate::leanh::lean_ctor_get(v___x_4298_, 0);
                        v_isSharedCheck_4312_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4298_)) as u8;
                        if v_isSharedCheck_4312_ == 0 {
                            v___x_4301_ = v___x_4298_;
                            v_isShared_4302_ = v_isSharedCheck_4312_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4299_);
                            crate::leanh::lean_dec(v___x_4298_);
                            v___x_4301_ = crate::leanh::lean_box(0);
                            v_isShared_4302_ = v_isSharedCheck_4312_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4298_, 0);
                        v_isSharedCheck_4320_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4298_)) as u8;
                        if v_isSharedCheck_4320_ == 0 {
                            v___x_4315_ = v___x_4298_;
                            v_isShared_4316_ = v_isSharedCheck_4320_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4313_);
                            crate::leanh::lean_dec(v___x_4298_);
                            v___x_4315_ = crate::leanh::lean_box(0);
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
                v_fst_4303_ = crate::leanh::lean_ctor_get(v_a_4299_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4303_) == 0 {
                    v_snd_4304_ = crate::leanh::lean_ctor_get(v_a_4299_, 1);
                    crate::leanh::lean_inc(v_snd_4304_);
                    crate::leanh::lean_dec(v_a_4299_);
                    if v_isShared_4302_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4301_, 0, v_snd_4304_);
                        v___x_4306_ = v___x_4301_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_snd_4304_);
                        v___x_4306_ = v_reuseFailAlloc_4307_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4303_);
                    crate::leanh::lean_dec(v_a_4299_);
                    v_val_4308_ = crate::leanh::lean_ctor_get(v_fst_4303_, 0);
                    crate::leanh::lean_inc(v_val_4308_);
                    crate::leanh::lean_dec_ref_known(v_fst_4303_, 1);
                    if v_isShared_4302_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4301_, 0, v_val_4308_);
                        v___x_4310_ = v___x_4301_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_val_4308_);
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
                    v_reuseFailAlloc_4319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
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
                    v_reuseFailAlloc_4328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
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
    mut v_ctx_4330_: *mut crate::leanh::LeanObject,
    mut v_t_4331_: *mut crate::leanh::LeanObject,
    mut v_init_4332_: *mut crate::leanh::LeanObject,
    mut v___y_4333_: *mut crate::leanh::LeanObject,
    mut v___y_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
    mut v___y_4341_: *mut crate::leanh::LeanObject,
    mut v___y_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4342_);
    crate::leanh::lean_dec_ref(v___y_4341_);
    crate::leanh::lean_dec(v___y_4340_);
    crate::leanh::lean_dec_ref(v___y_4339_);
    crate::leanh::lean_dec(v___y_4338_);
    crate::leanh::lean_dec_ref(v___y_4337_);
    crate::leanh::lean_dec(v___y_4336_);
    crate::leanh::lean_dec_ref(v___y_4335_);
    crate::leanh::lean_dec(v___y_4334_);
    crate::leanh::lean_dec(v___y_4333_);
    crate::leanh::lean_dec_ref(v_t_4331_);
    return v_res_4344_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0;
    v___x_4349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__6___closed__5;
    v___x_4350_ = l_Lean_Name_append(v___x_4349_, v___x_4348_);
    return v___x_4350_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(
    mut v_as_4351_: *mut crate::leanh::LeanObject,
    mut v_i_4352_: usize,
    mut v_stop_4353_: usize,
    mut v_b_4354_: *mut crate::leanh::LeanObject,
    mut v___y_4355_: *mut crate::leanh::LeanObject,
    mut v___y_4356_: *mut crate::leanh::LeanObject,
    mut v___y_4357_: *mut crate::leanh::LeanObject,
    mut v___y_4358_: *mut crate::leanh::LeanObject,
    mut v___y_4359_: *mut crate::leanh::LeanObject,
    mut v___y_4360_: *mut crate::leanh::LeanObject,
    mut v___y_4361_: *mut crate::leanh::LeanObject,
    mut v___y_4362_: *mut crate::leanh::LeanObject,
    mut v___y_4363_: *mut crate::leanh::LeanObject,
    mut v___y_4364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: usize = 0;
    let mut v___x_4369_: usize = 0;
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: u8 = 0;
    let mut v_a_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4397_: u8 = 0;
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4401_: u8 = 0;
    let mut v___y_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: u8 = 0;
    let mut v_a_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4421_: u8 = 0;
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4425_: u8 = 0;
    let mut v_a_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4429_: u8 = 0;
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4433_: u8 = 0;
    let mut v_options_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4435_: u8 = 0;
    let mut v_inheritedTraceOptions_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: u8 = 0;
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4445_: u8 = 0;
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4449_: u8 = 0;
    let mut v_a_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4371_ = lean_usize_dec_eq(v_i_4352_, v_stop_4353_);
                if v___x_4371_ == 0 {
                    v___x_4372_ = lean_array_uget_borrowed(v_as_4351_, v_i_4352_);
                    v___x_4373_ =
                        l_Lean_Meta_Grind_isKnownCaseSplit___redArg(v___x_4372_, v___y_4355_);
                    if crate::leanh::lean_obj_tag(v___x_4373_) == 0 {
                        v_a_4374_ = crate::leanh::lean_ctor_get(v___x_4373_, 0);
                        crate::leanh::lean_inc(v_a_4374_);
                        crate::leanh::lean_dec_ref_known(v___x_4373_, 1);
                        v___x_4375_ = (crate::leanh::lean_unbox(v_a_4374_) as u8);
                        crate::leanh::lean_dec(v_a_4374_);
                        if v___x_4375_ == 0 {
                            if crate::leanh::lean_obj_tag(v___x_4372_) == 2 {
                                v_a_4376_ = crate::leanh::lean_ctor_get(v___x_4372_, 0);
                                v_b_4377_ = crate::leanh::lean_ctor_get(v___x_4372_, 1);
                                v_eq_4378_ = crate::leanh::lean_ctor_get(v___x_4372_, 3);
                                v_options_4434_ = crate::leanh::lean_ctor_get(v___y_4363_, 2);
                                v_hasTrace_4435_ = crate::leanh::lean_ctor_get_uint8(
                                    v_options_4434_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
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
                                        crate::leanh::lean_ctor_get(v___y_4363_, 13);
                                    v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__0;
                                    v___x_4438_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17___closed__1);
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
                                        crate::leanh::lean_inc_ref(v_eq_4378_);
                                        v___x_4440_ = l_Lean_MessageData_ofExpr(v_eq_4378_);
                                        v___x_4441_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0___redArg(v___x_4437_, v___x_4440_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
                                        if crate::leanh::lean_obj_tag(v___x_4441_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_4441_, 1);
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
                                            crate::leanh::lean_dec_ref(v_b_4354_);
                                            v_a_4442_ = crate::leanh::lean_ctor_get(v___x_4441_, 0);
                                            v_isSharedCheck_4449_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4441_))
                                                    as u8;
                                            if v_isSharedCheck_4449_ == 0 {
                                                v___x_4444_ = v___x_4441_;
                                                v_isShared_4445_ = v_isSharedCheck_4449_;
                                                state = 10;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4442_);
                                                crate::leanh::lean_dec(v___x_4441_);
                                                v___x_4444_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_dec_ref(v_b_4354_);
                        v_a_4450_ = crate::leanh::lean_ctor_get(v___x_4373_, 0);
                        v_isSharedCheck_4457_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4373_)) as u8;
                        if v_isSharedCheck_4457_ == 0 {
                            v___x_4452_ = v___x_4373_;
                            v_isShared_4453_ = v_isSharedCheck_4457_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4450_);
                            crate::leanh::lean_dec(v___x_4373_);
                            v___x_4452_ = crate::leanh::lean_box(0);
                            v_isShared_4453_ = v_isSharedCheck_4457_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    v___x_4458_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4458_, 0, v_b_4354_);
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
                v___x_4391_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_4385_);
                crate::leanh::lean_inc_ref(v___y_4381_);
                crate::leanh::lean_inc(v___y_4383_);
                crate::leanh::lean_inc_ref(v___y_4380_);
                crate::leanh::lean_inc(v___y_4388_);
                crate::leanh::lean_inc_ref(v___y_4386_);
                crate::leanh::lean_inc(v___y_4389_);
                crate::leanh::lean_inc_ref(v___y_4384_);
                crate::leanh::lean_inc(v___y_4387_);
                crate::leanh::lean_inc(v___y_4382_);
                crate::leanh::lean_inc_ref(v_eq_4378_);
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
                if crate::leanh::lean_obj_tag(v___x_4392_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4392_, 1);
                    crate::leanh::lean_inc_ref(v___x_4372_);
                    v___x_4393_ = lean_array_push(v_b_4354_, v___x_4372_);
                    v_a_4367_ = v___x_4393_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4354_);
                    v_a_4394_ = crate::leanh::lean_ctor_get(v___x_4392_, 0);
                    v_isSharedCheck_4401_ = (!crate::leanh::lean_is_exclusive(v___x_4392_)) as u8;
                    if v_isSharedCheck_4401_ == 0 {
                        v___x_4396_ = v___x_4392_;
                        v_isShared_4397_ = v_isSharedCheck_4401_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4394_);
                        crate::leanh::lean_dec(v___x_4392_);
                        v___x_4396_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
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
                if crate::leanh::lean_obj_tag(v___x_4413_) == 0 {
                    v_a_4414_ = crate::leanh::lean_ctor_get(v___x_4413_, 0);
                    crate::leanh::lean_inc(v_a_4414_);
                    crate::leanh::lean_dec_ref_known(v___x_4413_, 1);
                    v___x_4415_ = l_Lean_Meta_Grind_getGeneration___redArg(v_b_4377_, v___y_4403_);
                    if crate::leanh::lean_obj_tag(v___x_4415_) == 0 {
                        v_a_4416_ = crate::leanh::lean_ctor_get(v___x_4415_, 0);
                        crate::leanh::lean_inc(v_a_4416_);
                        crate::leanh::lean_dec_ref_known(v___x_4415_, 1);
                        v___x_4417_ = lean_nat_dec_le(v_a_4414_, v_a_4416_);
                        if v___x_4417_ == 0 {
                            crate::leanh::lean_dec(v_a_4416_);
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
                            crate::leanh::lean_dec(v_a_4414_);
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
                        crate::leanh::lean_dec(v_a_4414_);
                        crate::leanh::lean_dec_ref(v_b_4354_);
                        v_a_4418_ = crate::leanh::lean_ctor_get(v___x_4415_, 0);
                        v_isSharedCheck_4425_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4415_)) as u8;
                        if v_isSharedCheck_4425_ == 0 {
                            v___x_4420_ = v___x_4415_;
                            v_isShared_4421_ = v_isSharedCheck_4425_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4418_);
                            crate::leanh::lean_dec(v___x_4415_);
                            v___x_4420_ = crate::leanh::lean_box(0);
                            v_isShared_4421_ = v_isSharedCheck_4425_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_4354_);
                    v_a_4426_ = crate::leanh::lean_ctor_get(v___x_4413_, 0);
                    v_isSharedCheck_4433_ = (!crate::leanh::lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4433_ == 0 {
                        v___x_4428_ = v___x_4413_;
                        v_isShared_4429_ = v_isSharedCheck_4433_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4426_);
                        crate::leanh::lean_dec(v___x_4413_);
                        v___x_4428_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
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
                    v_reuseFailAlloc_4432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
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
                    v_reuseFailAlloc_4448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
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
                    v_reuseFailAlloc_4456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
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
    mut v_as_4459_: *mut crate::leanh::LeanObject,
    mut v_i_4460_: *mut crate::leanh::LeanObject,
    mut v_stop_4461_: *mut crate::leanh::LeanObject,
    mut v_b_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
    mut v___y_4464_: *mut crate::leanh::LeanObject,
    mut v___y_4465_: *mut crate::leanh::LeanObject,
    mut v___y_4466_: *mut crate::leanh::LeanObject,
    mut v___y_4467_: *mut crate::leanh::LeanObject,
    mut v___y_4468_: *mut crate::leanh::LeanObject,
    mut v___y_4469_: *mut crate::leanh::LeanObject,
    mut v___y_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
    mut v___y_4472_: *mut crate::leanh::LeanObject,
    mut v___y_4473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4474_: usize = 0;
    let mut v_stop_boxed_4475_: usize = 0;
    let mut v_res_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4474_ = crate::leanh::lean_unbox_usize(v_i_4460_);
    crate::leanh::lean_dec(v_i_4460_);
    v_stop_boxed_4475_ = crate::leanh::lean_unbox_usize(v_stop_4461_);
    crate::leanh::lean_dec(v_stop_4461_);
    v_res_4476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_4459_, v_i_boxed_4474_, v_stop_boxed_4475_, v_b_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
    crate::leanh::lean_dec(v___y_4472_);
    crate::leanh::lean_dec_ref(v___y_4471_);
    crate::leanh::lean_dec(v___y_4470_);
    crate::leanh::lean_dec_ref(v___y_4469_);
    crate::leanh::lean_dec(v___y_4468_);
    crate::leanh::lean_dec_ref(v___y_4467_);
    crate::leanh::lean_dec(v___y_4466_);
    crate::leanh::lean_dec_ref(v___y_4465_);
    crate::leanh::lean_dec(v___y_4464_);
    crate::leanh::lean_dec(v___y_4463_);
    crate::leanh::lean_dec_ref(v_as_4459_);
    return v_res_4476_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8(
    mut v_as_4479_: *mut crate::leanh::LeanObject,
    mut v_start_4480_: *mut crate::leanh::LeanObject,
    mut v_stop_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
    mut v___y_4483_: *mut crate::leanh::LeanObject,
    mut v___y_4484_: *mut crate::leanh::LeanObject,
    mut v___y_4485_: *mut crate::leanh::LeanObject,
    mut v___y_4486_: *mut crate::leanh::LeanObject,
    mut v___y_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
    mut v___y_4489_: *mut crate::leanh::LeanObject,
    mut v___y_4490_: *mut crate::leanh::LeanObject,
    mut v___y_4491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    v___x_4493_ = l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___closed__0;
    v___x_4494_ = lean_nat_dec_lt(v_start_4480_, v_stop_4481_);
    if v___x_4494_ == 0 {
        let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4495_, 0, v___x_4493_);
        return v___x_4495_;
    } else {
        let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4497_: u8 = 0;
        v___x_4496_ = lean_array_get_size(v_as_4479_);
        v___x_4497_ = lean_nat_dec_le(v_stop_4481_, v___x_4496_);
        if v___x_4497_ == 0 {
            let mut v___x_4498_: u8 = 0;
            v___x_4498_ = lean_nat_dec_lt(v_start_4480_, v___x_4496_);
            if v___x_4498_ == 0 {
                let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4499_, 0, v___x_4493_);
                return v___x_4499_;
            } else {
                let mut v___x_4500_: usize = 0;
                let mut v___x_4501_: usize = 0;
                let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4500_ = lean_usize_of_nat(v_start_4480_);
                v___x_4501_ = lean_usize_of_nat(v___x_4496_);
                v___x_4502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_4479_, v___x_4500_, v___x_4501_, v___x_4493_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
                return v___x_4502_;
            }
        } else {
            let mut v___x_4503_: usize = 0;
            let mut v___x_4504_: usize = 0;
            let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4503_ = lean_usize_of_nat(v_start_4480_);
            v___x_4504_ = lean_usize_of_nat(v_stop_4481_);
            v___x_4505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8_spec__17(v_as_4479_, v___x_4503_, v___x_4504_, v___x_4493_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
            return v___x_4505_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Meta_Grind_mbtc_spec__8___boxed(
    mut v_as_4506_: *mut crate::leanh::LeanObject,
    mut v_start_4507_: *mut crate::leanh::LeanObject,
    mut v_stop_4508_: *mut crate::leanh::LeanObject,
    mut v___y_4509_: *mut crate::leanh::LeanObject,
    mut v___y_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
    mut v___y_4514_: *mut crate::leanh::LeanObject,
    mut v___y_4515_: *mut crate::leanh::LeanObject,
    mut v___y_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4518_);
    crate::leanh::lean_dec_ref(v___y_4517_);
    crate::leanh::lean_dec(v___y_4516_);
    crate::leanh::lean_dec_ref(v___y_4515_);
    crate::leanh::lean_dec(v___y_4514_);
    crate::leanh::lean_dec_ref(v___y_4513_);
    crate::leanh::lean_dec(v___y_4512_);
    crate::leanh::lean_dec_ref(v___y_4511_);
    crate::leanh::lean_dec(v___y_4510_);
    crate::leanh::lean_dec(v___y_4509_);
    crate::leanh::lean_dec(v_stop_4508_);
    crate::leanh::lean_dec(v_start_4507_);
    crate::leanh::lean_dec_ref(v_as_4506_);
    return v_res_4520_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = crate::leanh::lean_box(0);
    v___x_4522_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4523_ = lean_mk_array(v___x_4522_, v___x_4521_);
    return v___x_4523_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4524_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__0_once),
        _init_l_Lean_Meta_Grind_mbtc___closed__0,
    );
    v___x_4525_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4526_, 0, v___x_4525_);
    crate::leanh::lean_ctor_set(v___x_4526_, 1, v___x_4524_);
    return v___x_4526_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4527_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__1_once),
        _init_l_Lean_Meta_Grind_mbtc___closed__1,
    );
    v___x_4528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4528_, 0, v___x_4527_);
    crate::leanh::lean_ctor_set(v___x_4528_, 1, v___x_4527_);
    return v___x_4528_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4530_ = l_Lean_Meta_Grind_mbtc___closed__3;
    v___x_4531_ = l_Lean_stringToMessageData(v___x_4530_);
    return v___x_4531_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mbtc___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4533_ = l_Lean_Meta_Grind_mbtc___closed__5;
    v___x_4534_ = l_Lean_stringToMessageData(v___x_4533_);
    return v___x_4534_;
}
pub unsafe fn l_Lean_Meta_Grind_mbtc(
    mut v_ctx_4535_: *mut crate::leanh::LeanObject,
    mut v_a_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
    mut v_a_4542_: *mut crate::leanh::LeanObject,
    mut v_a_4543_: *mut crate::leanh::LeanObject,
    mut v_a_4544_: *mut crate::leanh::LeanObject,
    mut v_a_4545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4551_: u8 = 0;
    let mut v_mbtc_4552_: u8 = 0;
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4561_: u8 = 0;
    let mut v___x_4562_: u8 = 0;
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4572_: u8 = 0;
    let mut v_snd_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4578_: u8 = 0;
    let mut v___x_4579_: u8 = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4590_: u8 = 0;
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: u8 = 0;
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4594_: usize = 0;
    let mut v___x_4595_: usize = 0;
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4599_: u8 = 0;
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4604_: u8 = 0;
    let mut v_unused_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4609_: u8 = 0;
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_a_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v___y_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: u8 = 0;
    let mut v___y_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: u8 = 0;
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: u8 = 0;
    let mut v_toGoalState_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v_split_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splits_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: u8 = 0;
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut v___x_4657_: u8 = 0;
    let mut v___x_4658_: usize = 0;
    let mut v___x_4659_: usize = 0;
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: usize = 0;
    let mut v___x_4662_: usize = 0;
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splits_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4689_: u8 = 0;
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4694_: u8 = 0;
    let mut v_unused_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4699_: u8 = 0;
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4703_: u8 = 0;
    let mut v_reuseFailAlloc_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4706_: u8 = 0;
    let mut v_a_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4710_: u8 = 0;
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4714_: u8 = 0;
    let mut v_a_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4718_: u8 = 0;
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4722_: u8 = 0;
    let mut v_isSharedCheck_4723_: u8 = 0;
    let mut v_unused_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4728_: u8 = 0;
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4732_: u8 = 0;
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v_a_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4741_: u8 = 0;
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4745_: u8 = 0;
    let mut v___x_4746_: u8 = 0;
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4751_: u8 = 0;
    let mut v_isSharedCheck_4752_: u8 = 0;
    let mut v_a_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4756_: u8 = 0;
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4547_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4538_);
                if crate::leanh::lean_obj_tag(v___x_4547_) == 0 {
                    v_a_4548_ = crate::leanh::lean_ctor_get(v___x_4547_, 0);
                    v_isSharedCheck_4752_ = (!crate::leanh::lean_is_exclusive(v___x_4547_)) as u8;
                    if v_isSharedCheck_4752_ == 0 {
                        v___x_4550_ = v___x_4547_;
                        v_isShared_4551_ = v_isSharedCheck_4752_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4548_);
                        crate::leanh::lean_dec(v___x_4547_);
                        v___x_4550_ = crate::leanh::lean_box(0);
                        v_isShared_4551_ = v_isSharedCheck_4752_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ctx_4535_);
                    v_a_4753_ = crate::leanh::lean_ctor_get(v___x_4547_, 0);
                    v_isSharedCheck_4760_ = (!crate::leanh::lean_is_exclusive(v___x_4547_)) as u8;
                    if v_isSharedCheck_4760_ == 0 {
                        v___x_4755_ = v___x_4547_;
                        v_isShared_4756_ = v_isSharedCheck_4760_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4753_);
                        crate::leanh::lean_dec(v___x_4547_);
                        v___x_4755_ = crate::leanh::lean_box(0);
                        v_isShared_4756_ = v_isSharedCheck_4760_;
                        state = 37;
                        continue;
                    }
                }
            }
            1 => {
                v_mbtc_4552_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4548_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 18) as u32,
                );
                crate::leanh::lean_dec(v_a_4548_);
                if v_mbtc_4552_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_4535_);
                    v___x_4553_ = crate::leanh::lean_box((v_mbtc_4552_) as usize);
                    if v_isShared_4551_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4550_, 0, v___x_4553_);
                        v___x_4555_ = v___x_4550_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
                        v___x_4555_ = v_reuseFailAlloc_4556_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4550_);
                    v___x_4557_ =
                        l_Lean_Meta_Grind_checkMaxCaseSplit___redArg(v_a_4536_, v_a_4538_);
                    if crate::leanh::lean_obj_tag(v___x_4557_) == 0 {
                        v_a_4558_ = crate::leanh::lean_ctor_get(v___x_4557_, 0);
                        v_isSharedCheck_4751_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4557_)) as u8;
                        if v_isSharedCheck_4751_ == 0 {
                            v___x_4560_ = v___x_4557_;
                            v_isShared_4561_ = v_isSharedCheck_4751_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4558_);
                            crate::leanh::lean_dec(v___x_4557_);
                            v___x_4560_ = crate::leanh::lean_box(0);
                            v_isShared_4561_ = v_isSharedCheck_4751_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ctx_4535_);
                        return v___x_4557_;
                    }
                }
            }
            2 => {
                return v___x_4555_;
            }
            3 => {
                v___x_4562_ = (crate::leanh::lean_unbox(v_a_4558_) as u8);
                if v___x_4562_ == 0 {
                    crate::leanh::lean_del_object(v___x_4560_);
                    v___x_4563_ = lean_st_ref_get(v_a_4536_);
                    v_toGoalState_4564_ = crate::leanh::lean_ctor_get(v___x_4563_, 0);
                    crate::leanh::lean_inc_ref(v_toGoalState_4564_);
                    crate::leanh::lean_dec(v___x_4563_);
                    v_exprs_4565_ = crate::leanh::lean_ctor_get(v_toGoalState_4564_, 2);
                    crate::leanh::lean_inc_ref(v_exprs_4565_);
                    crate::leanh::lean_dec_ref(v_toGoalState_4564_);
                    v___x_4566_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4567_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec_ref(v_exprs_4565_);
                    if crate::leanh::lean_obj_tag(v___x_4568_) == 0 {
                        v_a_4569_ = crate::leanh::lean_ctor_get(v___x_4568_, 0);
                        v_isSharedCheck_4737_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4568_)) as u8;
                        if v_isSharedCheck_4737_ == 0 {
                            v___x_4571_ = v___x_4568_;
                            v_isShared_4572_ = v_isSharedCheck_4737_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4569_);
                            crate::leanh::lean_dec(v___x_4568_);
                            v___x_4571_ = crate::leanh::lean_box(0);
                            v_isShared_4572_ = v_isSharedCheck_4737_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4558_);
                        v_a_4738_ = crate::leanh::lean_ctor_get(v___x_4568_, 0);
                        v_isSharedCheck_4745_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4568_)) as u8;
                        if v_isSharedCheck_4745_ == 0 {
                            v___x_4740_ = v___x_4568_;
                            v_isShared_4741_ = v_isSharedCheck_4745_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4738_);
                            crate::leanh::lean_dec(v___x_4568_);
                            v___x_4740_ = crate::leanh::lean_box(0);
                            v_isShared_4741_ = v_isSharedCheck_4745_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4558_);
                    crate::leanh::lean_dec_ref(v_ctx_4535_);
                    v___x_4746_ = 0;
                    v___x_4747_ = crate::leanh::lean_box((v___x_4746_) as usize);
                    if v_isShared_4561_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4560_, 0, v___x_4747_);
                        v___x_4749_ = v___x_4560_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_4750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
                        v___x_4749_ = v_reuseFailAlloc_4750_;
                        state = 36;
                        continue;
                    }
                }
            }
            4 => {
                v_snd_4573_ = crate::leanh::lean_ctor_get(v_a_4569_, 1);
                crate::leanh::lean_inc(v_snd_4573_);
                crate::leanh::lean_dec(v_a_4569_);
                v_size_4574_ = crate::leanh::lean_ctor_get(v_snd_4573_, 0);
                v_buckets_4575_ = crate::leanh::lean_ctor_get(v_snd_4573_, 1);
                v_isSharedCheck_4736_ = (!crate::leanh::lean_is_exclusive(v_snd_4573_)) as u8;
                if v_isSharedCheck_4736_ == 0 {
                    v___x_4577_ = v_snd_4573_;
                    v_isShared_4578_ = v_isSharedCheck_4736_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4575_);
                    crate::leanh::lean_inc(v_size_4574_);
                    crate::leanh::lean_dec(v_snd_4573_);
                    v___x_4577_ = crate::leanh::lean_box(0);
                    v_isShared_4578_ = v_isSharedCheck_4736_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4579_ = lean_nat_dec_eq(v_size_4574_, v___x_4566_);
                if v___x_4579_ == 0 {
                    crate::leanh::lean_del_object(v___x_4571_);
                    crate::leanh::lean_dec(v_a_4558_);
                    v___x_4580_ = lean_st_ref_get(v_a_4536_);
                    v___x_4581_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4538_);
                    if crate::leanh::lean_obj_tag(v___x_4581_) == 0 {
                        v_a_4582_ = crate::leanh::lean_ctor_get(v___x_4581_, 0);
                        crate::leanh::lean_inc(v_a_4582_);
                        crate::leanh::lean_dec_ref_known(v___x_4581_, 1);
                        v_toGoalState_4646_ = crate::leanh::lean_ctor_get(v___x_4580_, 0);
                        v_isSharedCheck_4723_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4580_)) as u8;
                        if v_isSharedCheck_4723_ == 0 {
                            v_unused_4724_ = crate::leanh::lean_ctor_get(v___x_4580_, 1);
                            crate::leanh::lean_dec(v_unused_4724_);
                            v___x_4648_ = v___x_4580_;
                            v_isShared_4649_ = v_isSharedCheck_4723_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_toGoalState_4646_);
                            crate::leanh::lean_dec(v___x_4580_);
                            v___x_4648_ = crate::leanh::lean_box(0);
                            v_isShared_4649_ = v_isSharedCheck_4723_;
                            state = 18;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4580_);
                        crate::leanh::lean_del_object(v___x_4577_);
                        crate::leanh::lean_dec_ref(v_buckets_4575_);
                        crate::leanh::lean_dec(v_size_4574_);
                        v_a_4725_ = crate::leanh::lean_ctor_get(v___x_4581_, 0);
                        v_isSharedCheck_4732_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4581_)) as u8;
                        if v_isSharedCheck_4732_ == 0 {
                            v___x_4727_ = v___x_4581_;
                            v_isShared_4728_ = v_isSharedCheck_4732_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4725_);
                            crate::leanh::lean_dec(v___x_4581_);
                            v___x_4727_ = crate::leanh::lean_box(0);
                            v_isShared_4728_ = v_isSharedCheck_4732_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4577_);
                    crate::leanh::lean_dec_ref(v_buckets_4575_);
                    crate::leanh::lean_dec(v_size_4574_);
                    if v_isShared_4572_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4571_, 0, v_a_4558_);
                        v___x_4734_ = v___x_4571_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_4735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4558_);
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
                crate::leanh::lean_dec_ref(v___y_4584_);
                if crate::leanh::lean_obj_tag(v___x_4586_) == 0 {
                    v_a_4587_ = crate::leanh::lean_ctor_get(v___x_4586_, 0);
                    v_isSharedCheck_4618_ = (!crate::leanh::lean_is_exclusive(v___x_4586_)) as u8;
                    if v_isSharedCheck_4618_ == 0 {
                        v___x_4589_ = v___x_4586_;
                        v_isShared_4590_ = v_isSharedCheck_4618_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4587_);
                        crate::leanh::lean_dec(v___x_4586_);
                        v___x_4589_ = crate::leanh::lean_box(0);
                        v_isShared_4590_ = v_isSharedCheck_4618_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_4619_ = crate::leanh::lean_ctor_get(v___x_4586_, 0);
                    v_isSharedCheck_4626_ = (!crate::leanh::lean_is_exclusive(v___x_4586_)) as u8;
                    if v_isSharedCheck_4626_ == 0 {
                        v___x_4621_ = v___x_4586_;
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4619_);
                        crate::leanh::lean_dec(v___x_4586_);
                        v___x_4621_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_del_object(v___x_4589_);
                    v___x_4593_ = crate::leanh::lean_box(0);
                    v_sz_4594_ = lean_array_size(v_a_4587_);
                    v___x_4595_ = 0usize;
                    v___x_4596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mbtc_spec__9(v_a_4587_, v_sz_4594_, v___x_4595_, v___x_4593_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
                    crate::leanh::lean_dec(v_a_4587_);
                    if crate::leanh::lean_obj_tag(v___x_4596_) == 0 {
                        v_isSharedCheck_4604_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4596_)) as u8;
                        if v_isSharedCheck_4604_ == 0 {
                            v_unused_4605_ = crate::leanh::lean_ctor_get(v___x_4596_, 0);
                            crate::leanh::lean_dec(v_unused_4605_);
                            v___x_4598_ = v___x_4596_;
                            v_isShared_4599_ = v_isSharedCheck_4604_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4596_);
                            v___x_4598_ = crate::leanh::lean_box(0);
                            v_isShared_4599_ = v_isSharedCheck_4604_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_4606_ = crate::leanh::lean_ctor_get(v___x_4596_, 0);
                        v_isSharedCheck_4613_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4596_)) as u8;
                        if v_isSharedCheck_4613_ == 0 {
                            v___x_4608_ = v___x_4596_;
                            v_isShared_4609_ = v_isSharedCheck_4613_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4606_);
                            crate::leanh::lean_dec(v___x_4596_);
                            v___x_4608_ = crate::leanh::lean_box(0);
                            v_isShared_4609_ = v_isSharedCheck_4613_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4587_);
                    v___x_4614_ = crate::leanh::lean_box((v___x_4579_) as usize);
                    if v_isShared_4590_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4589_, 0, v___x_4614_);
                        v___x_4616_ = v___x_4589_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4614_);
                        v___x_4616_ = v_reuseFailAlloc_4617_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                v___x_4600_ = crate::leanh::lean_box((v_mbtc_4552_) as usize);
                if v_isShared_4599_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4598_, 0, v___x_4600_);
                    v___x_4602_ = v___x_4598_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4600_);
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
                    v_reuseFailAlloc_4612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
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
                    v_reuseFailAlloc_4625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
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
                crate::leanh::lean_dec(v___y_4631_);
                crate::leanh::lean_dec(v___y_4629_);
                v___y_4584_ = v___x_4632_;
                state = 6;
                continue;
            }
            16 => {
                v___x_4638_ = lean_nat_dec_le(v___y_4637_, v___y_4634_);
                if v___x_4638_ == 0 {
                    crate::leanh::lean_dec(v___y_4634_);
                    crate::leanh::lean_inc(v___y_4637_);
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
                    v___x_4643_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4644_ = lean_nat_sub(v___x_4641_, v___x_4643_);
                    v___x_4645_ = lean_nat_dec_le(v___x_4566_, v___x_4644_);
                    if v___x_4645_ == 0 {
                        crate::leanh::lean_inc(v___x_4644_);
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
                v_split_4650_ = crate::leanh::lean_ctor_get(v_toGoalState_4646_, 14);
                crate::leanh::lean_inc_ref(v_split_4650_);
                crate::leanh::lean_dec_ref(v_toGoalState_4646_);
                v_splits_4651_ = crate::leanh::lean_ctor_get(v_a_4582_, 0);
                crate::leanh::lean_inc(v_splits_4651_);
                crate::leanh::lean_dec(v_a_4582_);
                v_num_4652_ = crate::leanh::lean_ctor_get(v_split_4650_, 0);
                crate::leanh::lean_inc(v_num_4652_);
                crate::leanh::lean_dec_ref(v_split_4650_);
                v___x_4653_ = lean_nat_dec_lt(v_splits_4651_, v_num_4652_);
                crate::leanh::lean_dec(v_num_4652_);
                crate::leanh::lean_dec(v_splits_4651_);
                if v___x_4653_ == 0 {
                    crate::leanh::lean_del_object(v___x_4648_);
                    crate::leanh::lean_del_object(v___x_4577_);
                    v___x_4654_ = lean_mk_empty_array_with_capacity(v_size_4574_);
                    crate::leanh::lean_dec(v_size_4574_);
                    v___x_4655_ = lean_array_get_size(v_buckets_4575_);
                    v___x_4656_ = lean_nat_dec_lt(v___x_4566_, v___x_4655_);
                    if v___x_4656_ == 0 {
                        crate::leanh::lean_dec_ref(v_buckets_4575_);
                        v___y_4640_ = v___x_4654_;
                        state = 17;
                        continue;
                    } else {
                        v___x_4657_ = lean_nat_dec_le(v___x_4655_, v___x_4655_);
                        if v___x_4657_ == 0 {
                            if v___x_4656_ == 0 {
                                crate::leanh::lean_dec_ref(v_buckets_4575_);
                                v___y_4640_ = v___x_4654_;
                                state = 17;
                                continue;
                            } else {
                                v___x_4658_ = 0usize;
                                v___x_4659_ = lean_usize_of_nat(v___x_4655_);
                                v___x_4660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_4575_, v___x_4658_, v___x_4659_, v___x_4654_);
                                crate::leanh::lean_dec_ref(v_buckets_4575_);
                                v___y_4640_ = v___x_4660_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v___x_4661_ = 0usize;
                            v___x_4662_ = lean_usize_of_nat(v___x_4655_);
                            v___x_4663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_mbtc_spec__12(v_buckets_4575_, v___x_4661_, v___x_4662_, v___x_4654_);
                            crate::leanh::lean_dec_ref(v_buckets_4575_);
                            v___y_4640_ = v___x_4663_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_buckets_4575_);
                    crate::leanh::lean_dec(v_size_4574_);
                    v___x_4664_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4538_);
                    if crate::leanh::lean_obj_tag(v___x_4664_) == 0 {
                        v_a_4665_ = crate::leanh::lean_ctor_get(v___x_4664_, 0);
                        crate::leanh::lean_inc(v_a_4665_);
                        crate::leanh::lean_dec_ref_known(v___x_4664_, 1);
                        v___x_4666_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4540_);
                        if crate::leanh::lean_obj_tag(v___x_4666_) == 0 {
                            v_a_4667_ = crate::leanh::lean_ctor_get(v___x_4666_, 0);
                            v_isSharedCheck_4706_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4666_)) as u8;
                            if v_isSharedCheck_4706_ == 0 {
                                v___x_4669_ = v___x_4666_;
                                v_isShared_4670_ = v_isSharedCheck_4706_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4667_);
                                crate::leanh::lean_dec(v___x_4666_);
                                v___x_4669_ = crate::leanh::lean_box(0);
                                v_isShared_4670_ = v_isSharedCheck_4706_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4665_);
                            crate::leanh::lean_del_object(v___x_4648_);
                            crate::leanh::lean_del_object(v___x_4577_);
                            v_a_4707_ = crate::leanh::lean_ctor_get(v___x_4666_, 0);
                            v_isSharedCheck_4714_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4666_)) as u8;
                            if v_isSharedCheck_4714_ == 0 {
                                v___x_4709_ = v___x_4666_;
                                v_isShared_4710_ = v_isSharedCheck_4714_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4707_);
                                crate::leanh::lean_dec(v___x_4666_);
                                v___x_4709_ = crate::leanh::lean_box(0);
                                v_isShared_4710_ = v_isSharedCheck_4714_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4648_);
                        crate::leanh::lean_del_object(v___x_4577_);
                        v_a_4715_ = crate::leanh::lean_ctor_get(v___x_4664_, 0);
                        v_isSharedCheck_4722_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4664_)) as u8;
                        if v_isSharedCheck_4722_ == 0 {
                            v___x_4717_ = v___x_4664_;
                            v_isShared_4718_ = v_isSharedCheck_4722_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4715_);
                            crate::leanh::lean_dec(v___x_4664_);
                            v___x_4717_ = crate::leanh::lean_box(0);
                            v_isShared_4718_ = v_isSharedCheck_4722_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            19 => {
                v___x_4671_ = (crate::leanh::lean_unbox(v_a_4667_) as u8);
                crate::leanh::lean_dec(v_a_4667_);
                if v___x_4671_ == 0 {
                    crate::leanh::lean_dec(v_a_4665_);
                    crate::leanh::lean_del_object(v___x_4648_);
                    crate::leanh::lean_del_object(v___x_4577_);
                    v___x_4672_ = crate::leanh::lean_box((v___x_4579_) as usize);
                    if v_isShared_4670_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4669_, 0, v___x_4672_);
                        v___x_4674_ = v___x_4669_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_4675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4672_);
                        v___x_4674_ = v_reuseFailAlloc_4675_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4669_);
                    v_splits_4676_ = crate::leanh::lean_ctor_get(v_a_4665_, 0);
                    crate::leanh::lean_inc(v_splits_4676_);
                    crate::leanh::lean_dec(v_a_4665_);
                    v___x_4677_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__4_once),
                        _init_l_Lean_Meta_Grind_mbtc___closed__4,
                    );
                    v___x_4678_ = l_Nat_reprFast(v_splits_4676_);
                    v___x_4679_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4679_, 0, v___x_4678_);
                    v___x_4680_ = l_Lean_MessageData_ofFormat(v___x_4679_);
                    if v_isShared_4649_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4648_, 7);
                        crate::leanh::lean_ctor_set(v___x_4648_, 1, v___x_4680_);
                        crate::leanh::lean_ctor_set(v___x_4648_, 0, v___x_4677_);
                        v___x_4682_ = v___x_4648_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_4705_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 0, v___x_4677_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 1, v___x_4680_);
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
                v___x_4683_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mbtc___closed__6_once),
                    _init_l_Lean_Meta_Grind_mbtc___closed__6,
                );
                if v_isShared_4578_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4577_, 7);
                    crate::leanh::lean_ctor_set(v___x_4577_, 1, v___x_4683_);
                    crate::leanh::lean_ctor_set(v___x_4577_, 0, v___x_4682_);
                    v___x_4685_ = v___x_4577_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4704_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 1, v___x_4683_);
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
                if crate::leanh::lean_obj_tag(v___x_4686_) == 0 {
                    v_isSharedCheck_4694_ = (!crate::leanh::lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4694_ == 0 {
                        v_unused_4695_ = crate::leanh::lean_ctor_get(v___x_4686_, 0);
                        crate::leanh::lean_dec(v_unused_4695_);
                        v___x_4688_ = v___x_4686_;
                        v_isShared_4689_ = v_isSharedCheck_4694_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4686_);
                        v___x_4688_ = crate::leanh::lean_box(0);
                        v_isShared_4689_ = v_isSharedCheck_4694_;
                        state = 23;
                        continue;
                    }
                } else {
                    v_a_4696_ = crate::leanh::lean_ctor_get(v___x_4686_, 0);
                    v_isSharedCheck_4703_ = (!crate::leanh::lean_is_exclusive(v___x_4686_)) as u8;
                    if v_isSharedCheck_4703_ == 0 {
                        v___x_4698_ = v___x_4686_;
                        v_isShared_4699_ = v_isSharedCheck_4703_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4696_);
                        crate::leanh::lean_dec(v___x_4686_);
                        v___x_4698_ = crate::leanh::lean_box(0);
                        v_isShared_4699_ = v_isSharedCheck_4703_;
                        state = 25;
                        continue;
                    }
                }
            }
            23 => {
                v___x_4690_ = crate::leanh::lean_box((v___x_4579_) as usize);
                if v_isShared_4689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4688_, 0, v___x_4690_);
                    v___x_4692_ = v___x_4688_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4690_);
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
                    v_reuseFailAlloc_4702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_a_4696_);
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
                    v_reuseFailAlloc_4713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
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
                    v_reuseFailAlloc_4721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4715_);
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
                    v_reuseFailAlloc_4731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4725_);
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
                    v_reuseFailAlloc_4744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
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
                    v_reuseFailAlloc_4759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
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
    mut v_ctx_4761_: *mut crate::leanh::LeanObject,
    mut v_a_4762_: *mut crate::leanh::LeanObject,
    mut v_a_4763_: *mut crate::leanh::LeanObject,
    mut v_a_4764_: *mut crate::leanh::LeanObject,
    mut v_a_4765_: *mut crate::leanh::LeanObject,
    mut v_a_4766_: *mut crate::leanh::LeanObject,
    mut v_a_4767_: *mut crate::leanh::LeanObject,
    mut v_a_4768_: *mut crate::leanh::LeanObject,
    mut v_a_4769_: *mut crate::leanh::LeanObject,
    mut v_a_4770_: *mut crate::leanh::LeanObject,
    mut v_a_4771_: *mut crate::leanh::LeanObject,
    mut v_a_4772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4771_);
    crate::leanh::lean_dec_ref(v_a_4770_);
    crate::leanh::lean_dec(v_a_4769_);
    crate::leanh::lean_dec_ref(v_a_4768_);
    crate::leanh::lean_dec(v_a_4767_);
    crate::leanh::lean_dec_ref(v_a_4766_);
    crate::leanh::lean_dec(v_a_4765_);
    crate::leanh::lean_dec_ref(v_a_4764_);
    crate::leanh::lean_dec(v_a_4763_);
    crate::leanh::lean_dec(v_a_4762_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mbtc_spec__0(
    mut v_cls_4774_: *mut crate::leanh::LeanObject,
    mut v_msg_4775_: *mut crate::leanh::LeanObject,
    mut v___y_4776_: *mut crate::leanh::LeanObject,
    mut v___y_4777_: *mut crate::leanh::LeanObject,
    mut v___y_4778_: *mut crate::leanh::LeanObject,
    mut v___y_4779_: *mut crate::leanh::LeanObject,
    mut v___y_4780_: *mut crate::leanh::LeanObject,
    mut v___y_4781_: *mut crate::leanh::LeanObject,
    mut v___y_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
    mut v___y_4785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_cls_4788_: *mut crate::leanh::LeanObject,
    mut v_msg_4789_: *mut crate::leanh::LeanObject,
    mut v___y_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4799_);
    crate::leanh::lean_dec_ref(v___y_4798_);
    crate::leanh::lean_dec(v___y_4797_);
    crate::leanh::lean_dec_ref(v___y_4796_);
    crate::leanh::lean_dec(v___y_4795_);
    crate::leanh::lean_dec_ref(v___y_4794_);
    crate::leanh::lean_dec(v___y_4793_);
    crate::leanh::lean_dec_ref(v___y_4792_);
    crate::leanh::lean_dec(v___y_4791_);
    crate::leanh::lean_dec(v___y_4790_);
    return v_res_4801_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1(
    mut v_00_u03b2_4802_: *mut crate::leanh::LeanObject,
    mut v_m_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v_b_4805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4806_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1___redArg(v_m_4803_, v_a_4804_, v_b_4805_);
    return v___x_4806_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(
    mut v_00_u03b2_4807_: *mut crate::leanh::LeanObject,
    mut v_m_4808_: *mut crate::leanh::LeanObject,
    mut v_a_4809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___redArg(v_m_4808_, v_a_4809_);
    return v___x_4810_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2___boxed(
    mut v_00_u03b2_4811_: *mut crate::leanh::LeanObject,
    mut v_m_4812_: *mut crate::leanh::LeanObject,
    mut v_a_4813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4814_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2(
            v_00_u03b2_4811_,
            v_m_4812_,
            v_a_4813_,
        );
    crate::leanh::lean_dec_ref(v_a_4813_);
    crate::leanh::lean_dec_ref(v_m_4812_);
    return v_res_4814_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mbtc_spec__4(
    mut v_ctx_4815_: *mut crate::leanh::LeanObject,
    mut v_val_4816_: *mut crate::leanh::LeanObject,
    mut v___x_4817_: *mut crate::leanh::LeanObject,
    mut v___x_4818_: *mut crate::leanh::LeanObject,
    mut v_as_4819_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4820_: *mut crate::leanh::LeanObject,
    mut v_b_4821_: *mut crate::leanh::LeanObject,
    mut v_a_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
    mut v___y_4828_: *mut crate::leanh::LeanObject,
    mut v___y_4829_: *mut crate::leanh::LeanObject,
    mut v___y_4830_: *mut crate::leanh::LeanObject,
    mut v___y_4831_: *mut crate::leanh::LeanObject,
    mut v___y_4832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctx_4835_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_val_4836_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4837_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_4838_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_as_4839_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_as_x27_4840_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_b_4841_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_4842_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4843_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4844_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4845_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4846_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4847_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4848_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4849_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4850_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4851_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4852_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4853_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4852_);
    crate::leanh::lean_dec_ref(v___y_4851_);
    crate::leanh::lean_dec(v___y_4850_);
    crate::leanh::lean_dec_ref(v___y_4849_);
    crate::leanh::lean_dec(v___y_4848_);
    crate::leanh::lean_dec_ref(v___y_4847_);
    crate::leanh::lean_dec(v___y_4846_);
    crate::leanh::lean_dec_ref(v___y_4845_);
    crate::leanh::lean_dec(v___y_4844_);
    crate::leanh::lean_dec(v___y_4843_);
    crate::leanh::lean_dec(v_as_x27_4840_);
    crate::leanh::lean_dec(v_as_4839_);
    return v_res_4854_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5(
    mut v_00_u03b2_4855_: *mut crate::leanh::LeanObject,
    mut v_m_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v_b_4858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4859_ =
        l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5___redArg(
            v_m_4856_, v_a_4857_, v_b_4858_,
        );
    return v___x_4859_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(
    mut v_n_4860_: *mut crate::leanh::LeanObject,
    mut v_as_4861_: *mut crate::leanh::LeanObject,
    mut v_lo_4862_: *mut crate::leanh::LeanObject,
    mut v_hi_4863_: *mut crate::leanh::LeanObject,
    mut v_w_4864_: *mut crate::leanh::LeanObject,
    mut v_hlo_4865_: *mut crate::leanh::LeanObject,
    mut v_hhi_4866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4867_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___redArg(v_n_4860_, v_as_4861_, v_lo_4862_, v_hi_4863_);
    return v___x_4867_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10___boxed(
    mut v_n_4868_: *mut crate::leanh::LeanObject,
    mut v_as_4869_: *mut crate::leanh::LeanObject,
    mut v_lo_4870_: *mut crate::leanh::LeanObject,
    mut v_hi_4871_: *mut crate::leanh::LeanObject,
    mut v_w_4872_: *mut crate::leanh::LeanObject,
    mut v_hlo_4873_: *mut crate::leanh::LeanObject,
    mut v_hhi_4874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4875_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10(v_n_4868_, v_as_4869_, v_lo_4870_, v_hi_4871_, v_w_4872_, v_hlo_4873_, v_hhi_4874_);
    crate::leanh::lean_dec(v_hi_4871_);
    crate::leanh::lean_dec(v_n_4868_);
    return v_res_4875_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(
    mut v_00_u03b2_4876_: *mut crate::leanh::LeanObject,
    mut v_a_4877_: *mut crate::leanh::LeanObject,
    mut v_x_4878_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4879_: u8 = 0;
    v___x_4879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___redArg(v_a_4877_, v_x_4878_);
    return v___x_4879_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2___boxed(
    mut v_00_u03b2_4880_: *mut crate::leanh::LeanObject,
    mut v_a_4881_: *mut crate::leanh::LeanObject,
    mut v_x_4882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4883_: u8 = 0;
    let mut v_r_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4883_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__2(v_00_u03b2_4880_, v_a_4881_, v_x_4882_);
    crate::leanh::lean_dec(v_x_4882_);
    crate::leanh::lean_dec_ref(v_a_4881_);
    v_r_4884_ = crate::leanh::lean_box((v_res_4883_) as usize);
    return v_r_4884_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3(
    mut v_00_u03b2_4885_: *mut crate::leanh::LeanObject,
    mut v_data_4886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4887_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3___redArg(v_data_4886_);
    return v___x_4887_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(
    mut v_00_u03b2_4888_: *mut crate::leanh::LeanObject,
    mut v_a_4889_: *mut crate::leanh::LeanObject,
    mut v_x_4890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4891_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___redArg(v_a_4889_, v_x_4890_);
    return v___x_4891_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5___boxed(
    mut v_00_u03b2_4892_: *mut crate::leanh::LeanObject,
    mut v_a_4893_: *mut crate::leanh::LeanObject,
    mut v_x_4894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4895_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_mbtc_spec__2_spec__5(v_00_u03b2_4892_, v_a_4893_, v_x_4894_);
    crate::leanh::lean_dec(v_x_4894_);
    crate::leanh::lean_dec_ref(v_a_4893_);
    return v_res_4895_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(
    mut v_00_u03b2_4896_: *mut crate::leanh::LeanObject,
    mut v_a_4897_: *mut crate::leanh::LeanObject,
    mut v_x_4898_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4899_: u8 = 0;
    v___x_4899_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___redArg(v_a_4897_, v_x_4898_);
    return v___x_4899_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9___boxed(
    mut v_00_u03b2_4900_: *mut crate::leanh::LeanObject,
    mut v_a_4901_: *mut crate::leanh::LeanObject,
    mut v_x_4902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4903_: u8 = 0;
    let mut v_r_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4903_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__9(v_00_u03b2_4900_, v_a_4901_, v_x_4902_);
    crate::leanh::lean_dec(v_x_4902_);
    crate::leanh::lean_dec_ref(v_a_4901_);
    v_r_4904_ = crate::leanh::lean_box((v_res_4903_) as usize);
    return v_r_4904_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10(
    mut v_00_u03b2_4905_: *mut crate::leanh::LeanObject,
    mut v_data_4906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4907_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10___redArg(v_data_4906_);
    return v___x_4907_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11(
    mut v_00_u03b2_4908_: *mut crate::leanh::LeanObject,
    mut v_a_4909_: *mut crate::leanh::LeanObject,
    mut v_b_4910_: *mut crate::leanh::LeanObject,
    mut v_x_4911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4912_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__11___redArg(v_a_4909_, v_b_4910_, v_x_4911_);
    return v___x_4912_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(
    mut v_n_4913_: *mut crate::leanh::LeanObject,
    mut v_lo_4914_: *mut crate::leanh::LeanObject,
    mut v_hi_4915_: *mut crate::leanh::LeanObject,
    mut v_hhi_4916_: *mut crate::leanh::LeanObject,
    mut v_pivot_4917_: *mut crate::leanh::LeanObject,
    mut v_as_4918_: *mut crate::leanh::LeanObject,
    mut v_i_4919_: *mut crate::leanh::LeanObject,
    mut v_k_4920_: *mut crate::leanh::LeanObject,
    mut v_ilo_4921_: *mut crate::leanh::LeanObject,
    mut v_ik_4922_: *mut crate::leanh::LeanObject,
    mut v_w_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4924_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___redArg(v_hi_4915_, v_pivot_4917_, v_as_4918_, v_i_4919_, v_k_4920_);
    return v___x_4924_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20___boxed(
    mut v_n_4925_: *mut crate::leanh::LeanObject,
    mut v_lo_4926_: *mut crate::leanh::LeanObject,
    mut v_hi_4927_: *mut crate::leanh::LeanObject,
    mut v_hhi_4928_: *mut crate::leanh::LeanObject,
    mut v_pivot_4929_: *mut crate::leanh::LeanObject,
    mut v_as_4930_: *mut crate::leanh::LeanObject,
    mut v_i_4931_: *mut crate::leanh::LeanObject,
    mut v_k_4932_: *mut crate::leanh::LeanObject,
    mut v_ilo_4933_: *mut crate::leanh::LeanObject,
    mut v_ik_4934_: *mut crate::leanh::LeanObject,
    mut v_w_4935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4936_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_mbtc_spec__10_spec__20(v_n_4925_, v_lo_4926_, v_hi_4927_, v_hhi_4928_, v_pivot_4929_, v_as_4930_, v_i_4931_, v_k_4932_, v_ilo_4933_, v_ik_4934_, v_w_4935_);
    crate::leanh::lean_dec_ref(v_pivot_4929_);
    crate::leanh::lean_dec(v_hi_4927_);
    crate::leanh::lean_dec(v_lo_4926_);
    crate::leanh::lean_dec(v_n_4925_);
    return v_res_4936_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4(
    mut v_00_u03b2_4937_: *mut crate::leanh::LeanObject,
    mut v_i_4938_: *mut crate::leanh::LeanObject,
    mut v_source_4939_: *mut crate::leanh::LeanObject,
    mut v_target_4940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4941_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4___redArg(v_i_4938_, v_source_4939_, v_target_4940_);
    return v___x_4941_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12(
    mut v_00_u03b2_4942_: *mut crate::leanh::LeanObject,
    mut v_i_4943_: *mut crate::leanh::LeanObject,
    mut v_source_4944_: *mut crate::leanh::LeanObject,
    mut v_target_4945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4946_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12___redArg(v_i_4943_, v_source_4944_, v_target_4945_);
    return v___x_4946_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16(
    mut v_00_u03b2_4947_: *mut crate::leanh::LeanObject,
    mut v_x_4948_: *mut crate::leanh::LeanObject,
    mut v_x_4949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4950_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_mbtc_spec__1_spec__3_spec__4_spec__16___redArg(v_x_4948_, v_x_4949_);
    return v___x_4950_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21(
    mut v_00_u03b2_4951_: *mut crate::leanh::LeanObject,
    mut v_x_4952_: *mut crate::leanh::LeanObject,
    mut v_x_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4954_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mbtc_spec__5_spec__10_spec__12_spec__21___redArg(v_x_4952_, v_x_4953_);
    return v___x_4954_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark =
        _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_mainMark,
    );
    l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark =
        _init_l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_MBTC_0__Lean_Meta_Grind_otherMark,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_MBTC(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_MBTC(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_CastLike(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
}

// Lean compiler output
// Module: Lean.Compiler.LCNF.PrettyPrinter
// Imports: Lean.PrettyPrinter.Delaborator.Options Lean.Compiler.LCNF.Internalize Init.Data.Format.Macro
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_indentD;
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_CompilerM_run___redArg, l_Lean_Compiler_LCNF_getBinderName,
    l_Lean_Compiler_LCNF_getPurity___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::{
    initialize_Lean_Compiler_LCNF_Internalize, l_Lean_Compiler_LCNF_Code_internalize,
    l_Lean_Compiler_LCNF_Decl_internalize, runtime_initialize_Lean_Compiler_LCNF_Internalize,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_instantiateForall, l_Lean_Expr_isErased,
};
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isRuntime, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_isConst, l_Lean_Expr_isFVar, l_Lean_Expr_isProp,
    l_Lean_Expr_isType0, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Hygiene::l_Lean_pp_sanitizeNames;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey, l_Lean_Meta_ppExpr,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Options::{
    initialize_Lean_PrettyPrinter_Delaborator_Options, l_Lean_pp_all, l_Lean_pp_explicit,
    l_Lean_pp_funBinderTypes, l_Lean_pp_letVarTypes,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_Options,
};
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_length;
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_uint8_to_nat, lean_uint16_to_nat, lean_uint64_to_nat, lean_usize_add, lean_usize_dec_lt,
};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_uint32_to_nat,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 24) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        282574488338432 as *mut crate::leanh::LeanObject,
        72621647814721793 as *mut crate::leanh::LeanObject,
        65793 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1: u64 = 0;
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3_value:
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
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 151, 190, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [95, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 116, 111, 114, 95, 0]};
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [32, 35, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [111, 112, 114, 111, 106, 91, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [93, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [117, 112, 114, 111, 106, 91, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [115, 112, 114, 111, 106, 91, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [112, 97, 112, 32, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [114, 101, 115, 101, 116, 91, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 101, 117, 115, 101, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 105, 110, 32, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20_value: crate::leanh::LeanStringObject<
    1,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [33, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [98, 111, 120, 32, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [117, 110, 98, 111, 120, 32, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 115, 83, 104, 97, 114, 101, 100, 32, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 32, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2_value:
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
    m_data: [64, 38, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [108, 101, 116, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [32, 58, 61, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [59, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [102, 117, 110, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [106, 112, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [103, 111, 116, 111, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [124, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [32, 61, 62, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [124, 32, 95, 32, 61, 62, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [99, 97, 115, 101, 115, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [114, 101, 116, 117, 114, 110, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 138, 165, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 4,
        m_data: [226, 138, 165, 32, 58, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__15_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [111, 115, 101, 116, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [32, 91, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [93, 32, 58, 61, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__21_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [117, 115, 101, 116, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__23_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [115, 115, 101, 116, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__25_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__26_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [93, 32, 58, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__27_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__28_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [115, 101, 116, 84, 97, 103, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__29_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__28_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__30_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [105, 110, 99, 91, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__31_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__30_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 110, 99, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__33_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__34_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [91, 114, 101, 102, 93, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__34_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__35_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [91, 112, 101, 114, 115, 105, 115, 116, 101, 110, 116, 93, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [100, 101, 99, 91, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__37_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [100, 101, 99, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__39_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__40_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [32, 111, 98, 106, 115, 93, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__41_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [100, 101, 108, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__42_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__41_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 120, 116, 101, 114, 110, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 101, 102, 32, 0],
};
static mut l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(
    mut v_f_2545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2546_ = l_Std_Format_indentD(v_f_2545_);
    return v___x_2546_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(
    mut v_f_2550_: *mut crate::leanh::LeanObject,
    mut v_a_2551_: *mut crate::leanh::LeanObject,
    mut v_b_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
    mut v___y_2556_: *mut crate::leanh::LeanObject,
    mut v___y_2557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2559_ = crate::leanh::lean_ctor_get(v_a_2551_, 0);
                v_start_2560_ = crate::leanh::lean_ctor_get(v_a_2551_, 1);
                v_stop_2561_ = crate::leanh::lean_ctor_get(v_a_2551_, 2);
                v_isSharedCheck_2579_ = (!crate::leanh::lean_is_exclusive(v_a_2551_)) as u8;
                if v_isSharedCheck_2579_ == 0 {
                    v___x_2563_ = v_a_2551_;
                    v_isShared_2564_ = v_isSharedCheck_2579_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_2561_);
                    crate::leanh::lean_inc(v_start_2560_);
                    crate::leanh::lean_inc(v_array_2559_);
                    crate::leanh::lean_dec(v_a_2551_);
                    v___x_2563_ = crate::leanh::lean_box(0);
                    v_isShared_2564_ = v_isSharedCheck_2579_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2565_ = lean_nat_dec_lt(v_start_2560_, v_stop_2561_);
                if v___x_2565_ == 0 {
                    crate::leanh::lean_del_object(v___x_2563_);
                    crate::leanh::lean_dec(v_stop_2561_);
                    crate::leanh::lean_dec(v_start_2560_);
                    crate::leanh::lean_dec_ref(v_array_2559_);
                    crate::leanh::lean_dec_ref(v_f_2550_);
                    v___x_2566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2566_, 0, v_b_2552_);
                    return v___x_2566_;
                } else {
                    v___x_2567_ = lean_array_fget_borrowed(v_array_2559_, v_start_2560_);
                    crate::leanh::lean_inc_ref(v_f_2550_);
                    crate::leanh::lean_inc(v___y_2557_);
                    crate::leanh::lean_inc_ref(v___y_2556_);
                    crate::leanh::lean_inc(v___y_2555_);
                    crate::leanh::lean_inc_ref(v___y_2554_);
                    crate::leanh::lean_inc_ref(v___y_2553_);
                    crate::leanh::lean_inc(v___x_2567_);
                    v___x_2568_ = crate::leanh::lean_apply_7(
                        v_f_2550_,
                        v___x_2567_,
                        v___y_2553_,
                        v___y_2554_,
                        v___y_2555_,
                        v___y_2556_,
                        v___y_2557_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2568_) == 0 {
                        v_a_2569_ = crate::leanh::lean_ctor_get(v___x_2568_, 0);
                        crate::leanh::lean_inc(v_a_2569_);
                        crate::leanh::lean_dec_ref_known(v___x_2568_, 1);
                        v___x_2570_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2571_ = lean_nat_add(v_start_2560_, v___x_2570_);
                        crate::leanh::lean_dec(v_start_2560_);
                        if v_isShared_2564_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2563_, 1, v___x_2571_);
                            v___x_2573_ = v___x_2563_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2578_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_array_2559_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2571_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_stop_2561_);
                            v___x_2573_ = v_reuseFailAlloc_2578_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2563_);
                        crate::leanh::lean_dec(v_stop_2561_);
                        crate::leanh::lean_dec(v_start_2560_);
                        crate::leanh::lean_dec_ref(v_array_2559_);
                        crate::leanh::lean_dec(v_b_2552_);
                        crate::leanh::lean_dec_ref(v_f_2550_);
                        return v___x_2568_;
                    }
                }
            }
            2 => {
                v___x_2574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_2575_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2575_, 0, v_b_2552_);
                crate::leanh::lean_ctor_set(v___x_2575_, 1, v___x_2574_);
                v___x_2576_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2576_, 0, v___x_2575_);
                crate::leanh::lean_ctor_set(v___x_2576_, 1, v_a_2569_);
                v_a_2551_ = v___x_2573_;
                v_b_2552_ = v___x_2576_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___boxed(
    mut v_f_2580_: *mut crate::leanh::LeanObject,
    mut v_a_2581_: *mut crate::leanh::LeanObject,
    mut v_b_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
    mut v___y_2584_: *mut crate::leanh::LeanObject,
    mut v___y_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
    mut v___y_2587_: *mut crate::leanh::LeanObject,
    mut v___y_2588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2589_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_2580_, v_a_2581_, v_b_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
    crate::leanh::lean_dec(v___y_2587_);
    crate::leanh::lean_dec_ref(v___y_2586_);
    crate::leanh::lean_dec(v___y_2585_);
    crate::leanh::lean_dec_ref(v___y_2584_);
    crate::leanh::lean_dec_ref(v___y_2583_);
    return v_res_2589_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(
    mut v_as_2590_: *mut crate::leanh::LeanObject,
    mut v_f_2591_: *mut crate::leanh::LeanObject,
    mut v_a_2592_: *mut crate::leanh::LeanObject,
    mut v_a_2593_: *mut crate::leanh::LeanObject,
    mut v_a_2594_: *mut crate::leanh::LeanObject,
    mut v_a_2595_: *mut crate::leanh::LeanObject,
    mut v_a_2596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: u8 = 0;
    v___x_2598_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2599_ = lean_array_get_size(v_as_2590_);
    v___x_2600_ = lean_nat_dec_lt(v___x_2598_, v___x_2599_);
    if v___x_2600_ == 0 {
        let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_f_2591_);
        crate::leanh::lean_dec_ref(v_as_2590_);
        v___x_2601_ = crate::leanh::lean_box(0);
        v___x_2602_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2602_, 0, v___x_2601_);
        return v___x_2602_;
    } else {
        let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2603_ = lean_array_fget_borrowed(v_as_2590_, v___x_2598_);
        crate::leanh::lean_inc_ref(v_f_2591_);
        crate::leanh::lean_inc(v_a_2596_);
        crate::leanh::lean_inc_ref(v_a_2595_);
        crate::leanh::lean_inc(v_a_2594_);
        crate::leanh::lean_inc_ref(v_a_2593_);
        crate::leanh::lean_inc_ref(v_a_2592_);
        crate::leanh::lean_inc(v___x_2603_);
        v___x_2604_ = crate::leanh::lean_apply_7(
            v_f_2591_,
            v___x_2603_,
            v_a_2592_,
            v_a_2593_,
            v_a_2594_,
            v_a_2595_,
            v_a_2596_,
            crate::leanh::lean_box(0),
        );
        if crate::leanh::lean_obj_tag(v___x_2604_) == 0 {
            let mut v_a_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2605_ = crate::leanh::lean_ctor_get(v___x_2604_, 0);
            crate::leanh::lean_inc(v_a_2605_);
            crate::leanh::lean_dec_ref_known(v___x_2604_, 1);
            v___x_2606_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_2607_ = l_Array_toSubarray___redArg(v_as_2590_, v___x_2606_, v___x_2599_);
            v___x_2608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_2591_, v___x_2607_, v_a_2605_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
            return v___x_2608_;
        } else {
            crate::leanh::lean_dec_ref(v_f_2591_);
            crate::leanh::lean_dec_ref(v_as_2590_);
            return v___x_2604_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg___boxed(
    mut v_as_2609_: *mut crate::leanh::LeanObject,
    mut v_f_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
    mut v_a_2615_: *mut crate::leanh::LeanObject,
    mut v_a_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2617_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(
            v_as_2609_, v_f_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_,
        );
    crate::leanh::lean_dec(v_a_2615_);
    crate::leanh::lean_dec_ref(v_a_2614_);
    crate::leanh::lean_dec(v_a_2613_);
    crate::leanh::lean_dec_ref(v_a_2612_);
    crate::leanh::lean_dec_ref(v_a_2611_);
    return v_res_2617_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(
    mut v_00_u03b1_2618_: *mut crate::leanh::LeanObject,
    mut v_as_2619_: *mut crate::leanh::LeanObject,
    mut v_f_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
    mut v_a_2622_: *mut crate::leanh::LeanObject,
    mut v_a_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2627_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(
            v_as_2619_, v_f_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_,
        );
    return v___x_2627_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___boxed(
    mut v_00_u03b1_2628_: *mut crate::leanh::LeanObject,
    mut v_as_2629_: *mut crate::leanh::LeanObject,
    mut v_f_2630_: *mut crate::leanh::LeanObject,
    mut v_a_2631_: *mut crate::leanh::LeanObject,
    mut v_a_2632_: *mut crate::leanh::LeanObject,
    mut v_a_2633_: *mut crate::leanh::LeanObject,
    mut v_a_2634_: *mut crate::leanh::LeanObject,
    mut v_a_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2637_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(
        v_00_u03b1_2628_,
        v_as_2629_,
        v_f_2630_,
        v_a_2631_,
        v_a_2632_,
        v_a_2633_,
        v_a_2634_,
        v_a_2635_,
    );
    crate::leanh::lean_dec(v_a_2635_);
    crate::leanh::lean_dec_ref(v_a_2634_);
    crate::leanh::lean_dec(v_a_2633_);
    crate::leanh::lean_dec_ref(v_a_2632_);
    crate::leanh::lean_dec_ref(v_a_2631_);
    return v_res_2637_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(
    mut v_00_u03b1_2638_: *mut crate::leanh::LeanObject,
    mut v_f_2639_: *mut crate::leanh::LeanObject,
    mut v_inst_2640_: *mut crate::leanh::LeanObject,
    mut v_R_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
    mut v_b_2643_: *mut crate::leanh::LeanObject,
    mut v_c_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
    mut v___y_2648_: *mut crate::leanh::LeanObject,
    mut v___y_2649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_2639_, v_a_2642_, v_b_2643_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
    return v___x_2651_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___boxed(
    mut v_00_u03b1_2652_: *mut crate::leanh::LeanObject,
    mut v_f_2653_: *mut crate::leanh::LeanObject,
    mut v_inst_2654_: *mut crate::leanh::LeanObject,
    mut v_R_2655_: *mut crate::leanh::LeanObject,
    mut v_a_2656_: *mut crate::leanh::LeanObject,
    mut v_b_2657_: *mut crate::leanh::LeanObject,
    mut v_c_2658_: *mut crate::leanh::LeanObject,
    mut v___y_2659_: *mut crate::leanh::LeanObject,
    mut v___y_2660_: *mut crate::leanh::LeanObject,
    mut v___y_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(v_00_u03b1_2652_, v_f_2653_, v_inst_2654_, v_R_2655_, v_a_2656_, v_b_2657_, v_c_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
    crate::leanh::lean_dec(v___y_2663_);
    crate::leanh::lean_dec_ref(v___y_2662_);
    crate::leanh::lean_dec(v___y_2661_);
    crate::leanh::lean_dec_ref(v___y_2660_);
    crate::leanh::lean_dec_ref(v___y_2659_);
    return v_res_2665_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(
    mut v_f_2666_: *mut crate::leanh::LeanObject,
    mut v_pre_2667_: *mut crate::leanh::LeanObject,
    mut v_as_2668_: *mut crate::leanh::LeanObject,
    mut v_sz_2669_: usize,
    mut v_i_2670_: usize,
    mut v_b_2671_: *mut crate::leanh::LeanObject,
    mut v___y_2672_: *mut crate::leanh::LeanObject,
    mut v___y_2673_: *mut crate::leanh::LeanObject,
    mut v___y_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
    mut v___y_2676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: usize = 0;
    let mut v___x_2686_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2678_ = lean_usize_dec_lt(v_i_2670_, v_sz_2669_);
                if v___x_2678_ == 0 {
                    crate::leanh::lean_dec(v_pre_2667_);
                    crate::leanh::lean_dec_ref(v_f_2666_);
                    v___x_2679_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2679_, 0, v_b_2671_);
                    return v___x_2679_;
                } else {
                    v_a_2680_ = lean_array_uget_borrowed(v_as_2668_, v_i_2670_);
                    crate::leanh::lean_inc_ref(v_f_2666_);
                    crate::leanh::lean_inc(v___y_2676_);
                    crate::leanh::lean_inc_ref(v___y_2675_);
                    crate::leanh::lean_inc(v___y_2674_);
                    crate::leanh::lean_inc_ref(v___y_2673_);
                    crate::leanh::lean_inc_ref(v___y_2672_);
                    crate::leanh::lean_inc(v_a_2680_);
                    v___x_2681_ = crate::leanh::lean_apply_7(
                        v_f_2666_,
                        v_a_2680_,
                        v___y_2672_,
                        v___y_2673_,
                        v___y_2674_,
                        v___y_2675_,
                        v___y_2676_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2681_) == 0 {
                        v_a_2682_ = crate::leanh::lean_ctor_get(v___x_2681_, 0);
                        crate::leanh::lean_inc(v_a_2682_);
                        crate::leanh::lean_dec_ref_known(v___x_2681_, 1);
                        crate::leanh::lean_inc(v_pre_2667_);
                        v___x_2683_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2683_, 0, v_b_2671_);
                        crate::leanh::lean_ctor_set(v___x_2683_, 1, v_pre_2667_);
                        v___x_2684_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2684_, 0, v___x_2683_);
                        crate::leanh::lean_ctor_set(v___x_2684_, 1, v_a_2682_);
                        v___x_2685_ = 1usize;
                        v___x_2686_ = lean_usize_add(v_i_2670_, v___x_2685_);
                        v_i_2670_ = v___x_2686_;
                        v_b_2671_ = v___x_2684_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_2671_);
                        crate::leanh::lean_dec(v_pre_2667_);
                        crate::leanh::lean_dec_ref(v_f_2666_);
                        return v___x_2681_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg___boxed(
    mut v_f_2688_: *mut crate::leanh::LeanObject,
    mut v_pre_2689_: *mut crate::leanh::LeanObject,
    mut v_as_2690_: *mut crate::leanh::LeanObject,
    mut v_sz_2691_: *mut crate::leanh::LeanObject,
    mut v_i_2692_: *mut crate::leanh::LeanObject,
    mut v_b_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
    mut v___y_2695_: *mut crate::leanh::LeanObject,
    mut v___y_2696_: *mut crate::leanh::LeanObject,
    mut v___y_2697_: *mut crate::leanh::LeanObject,
    mut v___y_2698_: *mut crate::leanh::LeanObject,
    mut v___y_2699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2700_: usize = 0;
    let mut v_i_boxed_2701_: usize = 0;
    let mut v_res_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2700_ = crate::leanh::lean_unbox_usize(v_sz_2691_);
    crate::leanh::lean_dec(v_sz_2691_);
    v_i_boxed_2701_ = crate::leanh::lean_unbox_usize(v_i_2692_);
    crate::leanh::lean_dec(v_i_2692_);
    v_res_2702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_2688_, v_pre_2689_, v_as_2690_, v_sz_boxed_2700_, v_i_boxed_2701_, v_b_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
    crate::leanh::lean_dec(v___y_2698_);
    crate::leanh::lean_dec_ref(v___y_2697_);
    crate::leanh::lean_dec(v___y_2696_);
    crate::leanh::lean_dec_ref(v___y_2695_);
    crate::leanh::lean_dec_ref(v___y_2694_);
    crate::leanh::lean_dec_ref(v_as_2690_);
    return v_res_2702_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(
    mut v_pre_2703_: *mut crate::leanh::LeanObject,
    mut v_as_2704_: *mut crate::leanh::LeanObject,
    mut v_f_2705_: *mut crate::leanh::LeanObject,
    mut v_a_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
    mut v_a_2708_: *mut crate::leanh::LeanObject,
    mut v_a_2709_: *mut crate::leanh::LeanObject,
    mut v_a_2710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_result_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2713_: usize = 0;
    let mut v___x_2714_: usize = 0;
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_result_2712_ = crate::leanh::lean_box(0);
    v_sz_2713_ = lean_array_size(v_as_2704_);
    v___x_2714_ = 0usize;
    v___x_2715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_2705_, v_pre_2703_, v_as_2704_, v_sz_2713_, v___x_2714_, v_result_2712_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
    return v___x_2715_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg___boxed(
    mut v_pre_2716_: *mut crate::leanh::LeanObject,
    mut v_as_2717_: *mut crate::leanh::LeanObject,
    mut v_f_2718_: *mut crate::leanh::LeanObject,
    mut v_a_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_a_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2725_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(
            v_pre_2716_,
            v_as_2717_,
            v_f_2718_,
            v_a_2719_,
            v_a_2720_,
            v_a_2721_,
            v_a_2722_,
            v_a_2723_,
        );
    crate::leanh::lean_dec(v_a_2723_);
    crate::leanh::lean_dec_ref(v_a_2722_);
    crate::leanh::lean_dec(v_a_2721_);
    crate::leanh::lean_dec_ref(v_a_2720_);
    crate::leanh::lean_dec_ref(v_a_2719_);
    crate::leanh::lean_dec_ref(v_as_2717_);
    return v_res_2725_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(
    mut v_00_u03b1_2726_: *mut crate::leanh::LeanObject,
    mut v_pre_2727_: *mut crate::leanh::LeanObject,
    mut v_as_2728_: *mut crate::leanh::LeanObject,
    mut v_f_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
    mut v_a_2732_: *mut crate::leanh::LeanObject,
    mut v_a_2733_: *mut crate::leanh::LeanObject,
    mut v_a_2734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2736_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(
            v_pre_2727_,
            v_as_2728_,
            v_f_2729_,
            v_a_2730_,
            v_a_2731_,
            v_a_2732_,
            v_a_2733_,
            v_a_2734_,
        );
    return v___x_2736_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___boxed(
    mut v_00_u03b1_2737_: *mut crate::leanh::LeanObject,
    mut v_pre_2738_: *mut crate::leanh::LeanObject,
    mut v_as_2739_: *mut crate::leanh::LeanObject,
    mut v_f_2740_: *mut crate::leanh::LeanObject,
    mut v_a_2741_: *mut crate::leanh::LeanObject,
    mut v_a_2742_: *mut crate::leanh::LeanObject,
    mut v_a_2743_: *mut crate::leanh::LeanObject,
    mut v_a_2744_: *mut crate::leanh::LeanObject,
    mut v_a_2745_: *mut crate::leanh::LeanObject,
    mut v_a_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2747_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(
        v_00_u03b1_2737_,
        v_pre_2738_,
        v_as_2739_,
        v_f_2740_,
        v_a_2741_,
        v_a_2742_,
        v_a_2743_,
        v_a_2744_,
        v_a_2745_,
    );
    crate::leanh::lean_dec(v_a_2745_);
    crate::leanh::lean_dec_ref(v_a_2744_);
    crate::leanh::lean_dec(v_a_2743_);
    crate::leanh::lean_dec_ref(v_a_2742_);
    crate::leanh::lean_dec_ref(v_a_2741_);
    crate::leanh::lean_dec_ref(v_as_2739_);
    return v_res_2747_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(
    mut v_00_u03b1_2748_: *mut crate::leanh::LeanObject,
    mut v_f_2749_: *mut crate::leanh::LeanObject,
    mut v_pre_2750_: *mut crate::leanh::LeanObject,
    mut v_as_2751_: *mut crate::leanh::LeanObject,
    mut v_sz_2752_: usize,
    mut v_i_2753_: usize,
    mut v_b_2754_: *mut crate::leanh::LeanObject,
    mut v___y_2755_: *mut crate::leanh::LeanObject,
    mut v___y_2756_: *mut crate::leanh::LeanObject,
    mut v___y_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_2749_, v_pre_2750_, v_as_2751_, v_sz_2752_, v_i_2753_, v_b_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
    return v___x_2761_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___boxed(
    mut v_00_u03b1_2762_: *mut crate::leanh::LeanObject,
    mut v_f_2763_: *mut crate::leanh::LeanObject,
    mut v_pre_2764_: *mut crate::leanh::LeanObject,
    mut v_as_2765_: *mut crate::leanh::LeanObject,
    mut v_sz_2766_: *mut crate::leanh::LeanObject,
    mut v_i_2767_: *mut crate::leanh::LeanObject,
    mut v_b_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
    mut v___y_2770_: *mut crate::leanh::LeanObject,
    mut v___y_2771_: *mut crate::leanh::LeanObject,
    mut v___y_2772_: *mut crate::leanh::LeanObject,
    mut v___y_2773_: *mut crate::leanh::LeanObject,
    mut v___y_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2775_: usize = 0;
    let mut v_i_boxed_2776_: usize = 0;
    let mut v_res_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2775_ = crate::leanh::lean_unbox_usize(v_sz_2766_);
    crate::leanh::lean_dec(v_sz_2766_);
    v_i_boxed_2776_ = crate::leanh::lean_unbox_usize(v_i_2767_);
    crate::leanh::lean_dec(v_i_2767_);
    v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(v_00_u03b1_2762_, v_f_2763_, v_pre_2764_, v_as_2765_, v_sz_boxed_2775_, v_i_boxed_2776_, v_b_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
    crate::leanh::lean_dec(v___y_2773_);
    crate::leanh::lean_dec_ref(v___y_2772_);
    crate::leanh::lean_dec(v___y_2771_);
    crate::leanh::lean_dec_ref(v___y_2770_);
    crate::leanh::lean_dec_ref(v___y_2769_);
    crate::leanh::lean_dec_ref(v_as_2765_);
    return v_res_2777_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
    mut v_fvarId_2778_: *mut crate::leanh::LeanObject,
    mut v_a_2779_: *mut crate::leanh::LeanObject,
    mut v_a_2780_: *mut crate::leanh::LeanObject,
    mut v_a_2781_: *mut crate::leanh::LeanObject,
    mut v_a_2782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: u8 = 0;
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut v_a_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v___y_2801_: u8 = 0;
    let mut v___x_2802_: u8 = 0;
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: u8 = 0;
    let mut v___x_2812_: u8 = 0;
    let mut v_isSharedCheck_2813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_2778_);
                v___x_2784_ = l_Lean_Compiler_LCNF_getBinderName(
                    v_fvarId_2778_,
                    v_a_2779_,
                    v_a_2780_,
                    v_a_2781_,
                    v_a_2782_,
                );
                if crate::leanh::lean_obj_tag(v___x_2784_) == 0 {
                    crate::leanh::lean_dec(v_fvarId_2778_);
                    v_a_2785_ = crate::leanh::lean_ctor_get(v___x_2784_, 0);
                    v_isSharedCheck_2795_ = (!crate::leanh::lean_is_exclusive(v___x_2784_)) as u8;
                    if v_isSharedCheck_2795_ == 0 {
                        v___x_2787_ = v___x_2784_;
                        v_isShared_2788_ = v_isSharedCheck_2795_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2785_);
                        crate::leanh::lean_dec(v___x_2784_);
                        v___x_2787_ = crate::leanh::lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_2795_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2796_ = crate::leanh::lean_ctor_get(v___x_2784_, 0);
                    v_isSharedCheck_2813_ = (!crate::leanh::lean_is_exclusive(v___x_2784_)) as u8;
                    if v_isSharedCheck_2813_ == 0 {
                        v___x_2798_ = v___x_2784_;
                        v_isShared_2799_ = v_isSharedCheck_2813_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2796_);
                        crate::leanh::lean_dec(v___x_2784_);
                        v___x_2798_ = crate::leanh::lean_box(0);
                        v_isShared_2799_ = v_isSharedCheck_2813_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2789_ = 1;
                v___x_2790_ = l_Lean_Name_toString(v_a_2785_, v___x_2789_);
                v___x_2791_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2791_, 0, v___x_2790_);
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2791_);
                    v___x_2793_ = v___x_2787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
                    v___x_2793_ = v_reuseFailAlloc_2794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2793_;
            }
            3 => {
                v___x_2811_ = l_Lean_Exception_isInterrupt(v_a_2796_);
                if v___x_2811_ == 0 {
                    crate::leanh::lean_inc(v_a_2796_);
                    v___x_2812_ = l_Lean_Exception_isRuntime(v_a_2796_);
                    v___y_2801_ = v___x_2812_;
                    state = 4;
                    continue;
                } else {
                    v___y_2801_ = v___x_2811_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_2801_ == 0 {
                    crate::leanh::lean_dec(v_a_2796_);
                    v___x_2802_ = 1;
                    v___x_2803_ = l_Lean_Name_toString(v_fvarId_2778_, v___x_2802_);
                    v___x_2804_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2804_, 0, v___x_2803_);
                    if v_isShared_2799_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2798_, 0);
                        crate::leanh::lean_ctor_set(v___x_2798_, 0, v___x_2804_);
                        v___x_2806_ = v___x_2798_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2807_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
                        v___x_2806_ = v_reuseFailAlloc_2807_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_2778_);
                    if v_isShared_2799_ == 0 {
                        v___x_2809_ = v___x_2798_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2810_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2796_);
                        v___x_2809_ = v_reuseFailAlloc_2810_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2806_;
            }
            6 => {
                return v___x_2809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppFVar___redArg___boxed(
    mut v_fvarId_2814_: *mut crate::leanh::LeanObject,
    mut v_a_2815_: *mut crate::leanh::LeanObject,
    mut v_a_2816_: *mut crate::leanh::LeanObject,
    mut v_a_2817_: *mut crate::leanh::LeanObject,
    mut v_a_2818_: *mut crate::leanh::LeanObject,
    mut v_a_2819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2820_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
        v_fvarId_2814_,
        v_a_2815_,
        v_a_2816_,
        v_a_2817_,
        v_a_2818_,
    );
    crate::leanh::lean_dec(v_a_2818_);
    crate::leanh::lean_dec_ref(v_a_2817_);
    crate::leanh::lean_dec(v_a_2816_);
    crate::leanh::lean_dec_ref(v_a_2815_);
    return v_res_2820_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppFVar(
    mut v_fvarId_2821_: *mut crate::leanh::LeanObject,
    mut v_a_2822_: *mut crate::leanh::LeanObject,
    mut v_a_2823_: *mut crate::leanh::LeanObject,
    mut v_a_2824_: *mut crate::leanh::LeanObject,
    mut v_a_2825_: *mut crate::leanh::LeanObject,
    mut v_a_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2828_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
        v_fvarId_2821_,
        v_a_2823_,
        v_a_2824_,
        v_a_2825_,
        v_a_2826_,
    );
    return v___x_2828_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppFVar___boxed(
    mut v_fvarId_2829_: *mut crate::leanh::LeanObject,
    mut v_a_2830_: *mut crate::leanh::LeanObject,
    mut v_a_2831_: *mut crate::leanh::LeanObject,
    mut v_a_2832_: *mut crate::leanh::LeanObject,
    mut v_a_2833_: *mut crate::leanh::LeanObject,
    mut v_a_2834_: *mut crate::leanh::LeanObject,
    mut v_a_2835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_Lean_Compiler_LCNF_PP_ppFVar(
        v_fvarId_2829_,
        v_a_2830_,
        v_a_2831_,
        v_a_2832_,
        v_a_2833_,
        v_a_2834_,
    );
    crate::leanh::lean_dec(v_a_2834_);
    crate::leanh::lean_dec_ref(v_a_2833_);
    crate::leanh::lean_dec(v_a_2832_);
    crate::leanh::lean_dec_ref(v_a_2831_);
    crate::leanh::lean_dec_ref(v_a_2830_);
    return v_res_2836_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1() -> u64 {
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: u64 = 0;
    v___x_2843_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0;
    v___x_2844_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2843_);
    return v___x_2844_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2845_: u64 = 0;
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2845_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1,
    );
    v___x_2846_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0;
    v___x_2847_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_2847_, 0, v___x_2846_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_2847_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2845_,
    );
    return v___x_2847_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2850_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2850_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2851_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4,
    );
    v___x_2852_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2852_, 0, v___x_2851_);
    return v___x_2852_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2853_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5,
    );
    v___x_2854_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2855_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2855_, 0, v___x_2854_);
    crate::leanh::lean_ctor_set(v___x_2855_, 1, v___x_2854_);
    crate::leanh::lean_ctor_set(v___x_2855_, 2, v___x_2854_);
    crate::leanh::lean_ctor_set(v___x_2855_, 3, v___x_2854_);
    crate::leanh::lean_ctor_set(v___x_2855_, 4, v___x_2853_);
    crate::leanh::lean_ctor_set(v___x_2855_, 5, v___x_2853_);
    crate::leanh::lean_ctor_set(v___x_2855_, 6, v___x_2853_);
    crate::leanh::lean_ctor_set(v___x_2855_, 7, v___x_2853_);
    crate::leanh::lean_ctor_set(v___x_2855_, 8, v___x_2853_);
    crate::leanh::lean_ctor_set(v___x_2855_, 9, v___x_2853_);
    return v___x_2855_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2856_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5,
    );
    v___x_2857_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2857_, 0, v___x_2856_);
    crate::leanh::lean_ctor_set(v___x_2857_, 1, v___x_2856_);
    crate::leanh::lean_ctor_set(v___x_2857_, 2, v___x_2856_);
    crate::leanh::lean_ctor_set(v___x_2857_, 3, v___x_2856_);
    crate::leanh::lean_ctor_set(v___x_2857_, 4, v___x_2856_);
    crate::leanh::lean_ctor_set(v___x_2857_, 5, v___x_2856_);
    return v___x_2857_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2858_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2859_ = lean_mk_empty_array_with_capacity(v___x_2858_);
    v___x_2860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2860_, 0, v___x_2859_);
    return v___x_2860_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2861_: usize = 0;
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2861_ = 5usize;
    v___x_2862_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2863_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2864_ = lean_mk_empty_array_with_capacity(v___x_2863_);
    v___x_2865_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8,
    );
    v___x_2866_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2866_, 0, v___x_2865_);
    crate::leanh::lean_ctor_set(v___x_2866_, 1, v___x_2864_);
    crate::leanh::lean_ctor_set(v___x_2866_, 2, v___x_2862_);
    crate::leanh::lean_ctor_set(v___x_2866_, 3, v___x_2862_);
    crate::leanh::lean_ctor_set_usize(v___x_2866_, 4, v___x_2861_);
    return v___x_2866_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2867_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5,
    );
    v___x_2868_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2868_, 0, v___x_2867_);
    crate::leanh::lean_ctor_set(v___x_2868_, 1, v___x_2867_);
    crate::leanh::lean_ctor_set(v___x_2868_, 2, v___x_2867_);
    crate::leanh::lean_ctor_set(v___x_2868_, 3, v___x_2867_);
    crate::leanh::lean_ctor_set(v___x_2868_, 4, v___x_2867_);
    return v___x_2868_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10,
    );
    v___x_2870_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9,
    );
    v___x_2871_ = crate::leanh::lean_box(1);
    v___x_2872_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7,
    );
    v___x_2873_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6,
    );
    v___x_2874_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2874_, 0, v___x_2873_);
    crate::leanh::lean_ctor_set(v___x_2874_, 1, v___x_2872_);
    crate::leanh::lean_ctor_set(v___x_2874_, 2, v___x_2871_);
    crate::leanh::lean_ctor_set(v___x_2874_, 3, v___x_2870_);
    crate::leanh::lean_ctor_set(v___x_2874_, 4, v___x_2869_);
    return v___x_2874_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
    mut v_e_2875_: *mut crate::leanh::LeanObject,
    mut v_a_2876_: *mut crate::leanh::LeanObject,
    mut v_a_2877_: *mut crate::leanh::LeanObject,
    mut v_a_2878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    let mut v___x_2882_: u8 = 0;
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2894_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2880_ = crate::leanh::lean_box(1);
                v___x_2881_ = 0;
                v___x_2882_ = 1;
                v___x_2883_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2,
                );
                v___x_2884_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2885_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3;
                v___x_2886_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_a_2876_);
                v___x_2887_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2887_, 0, v___x_2883_);
                crate::leanh::lean_ctor_set(v___x_2887_, 1, v___x_2880_);
                crate::leanh::lean_ctor_set(v___x_2887_, 2, v_a_2876_);
                crate::leanh::lean_ctor_set(v___x_2887_, 3, v___x_2885_);
                crate::leanh::lean_ctor_set(v___x_2887_, 4, v___x_2886_);
                crate::leanh::lean_ctor_set(v___x_2887_, 5, v___x_2884_);
                crate::leanh::lean_ctor_set(v___x_2887_, 6, v___x_2886_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2887_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_2881_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2887_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_2881_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2887_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_2881_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2887_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_2882_,
                );
                v___x_2888_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once
                    ),
                    _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11,
                );
                v___x_2889_ = lean_st_mk_ref(v___x_2888_);
                v___x_2890_ =
                    l_Lean_Meta_ppExpr(v_e_2875_, v___x_2887_, v___x_2889_, v_a_2877_, v_a_2878_);
                crate::leanh::lean_dec_ref_known(v___x_2887_, 7);
                if crate::leanh::lean_obj_tag(v___x_2890_) == 0 {
                    v_a_2891_ = crate::leanh::lean_ctor_get(v___x_2890_, 0);
                    v_isSharedCheck_2899_ = (!crate::leanh::lean_is_exclusive(v___x_2890_)) as u8;
                    if v_isSharedCheck_2899_ == 0 {
                        v___x_2893_ = v___x_2890_;
                        v_isShared_2894_ = v_isSharedCheck_2899_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2891_);
                        crate::leanh::lean_dec(v___x_2890_);
                        v___x_2893_ = crate::leanh::lean_box(0);
                        v_isShared_2894_ = v_isSharedCheck_2899_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2889_);
                    return v___x_2890_;
                }
            }
            1 => {
                v___x_2895_ = lean_st_ref_get(v___x_2889_);
                crate::leanh::lean_dec(v___x_2889_);
                crate::leanh::lean_dec(v___x_2895_);
                if v_isShared_2894_ == 0 {
                    v___x_2897_ = v___x_2893_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2898_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2891_);
                    v___x_2897_ = v_reuseFailAlloc_2898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(
    mut v_e_2900_: *mut crate::leanh::LeanObject,
    mut v_a_2901_: *mut crate::leanh::LeanObject,
    mut v_a_2902_: *mut crate::leanh::LeanObject,
    mut v_a_2903_: *mut crate::leanh::LeanObject,
    mut v_a_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2905_ =
        l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
    crate::leanh::lean_dec(v_a_2903_);
    crate::leanh::lean_dec_ref(v_a_2902_);
    crate::leanh::lean_dec_ref(v_a_2901_);
    return v_res_2905_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppExpr(
    mut v_e_2906_: *mut crate::leanh::LeanObject,
    mut v_a_2907_: *mut crate::leanh::LeanObject,
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2913_ =
        l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_2906_, v_a_2907_, v_a_2910_, v_a_2911_);
    return v___x_2913_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppExpr___boxed(
    mut v_e_2914_: *mut crate::leanh::LeanObject,
    mut v_a_2915_: *mut crate::leanh::LeanObject,
    mut v_a_2916_: *mut crate::leanh::LeanObject,
    mut v_a_2917_: *mut crate::leanh::LeanObject,
    mut v_a_2918_: *mut crate::leanh::LeanObject,
    mut v_a_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Lean_Compiler_LCNF_PP_ppExpr(
        v_e_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_,
    );
    crate::leanh::lean_dec(v_a_2919_);
    crate::leanh::lean_dec_ref(v_a_2918_);
    crate::leanh::lean_dec(v_a_2917_);
    crate::leanh::lean_dec_ref(v_a_2916_);
    crate::leanh::lean_dec_ref(v_a_2915_);
    return v_res_2921_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
    mut v_opts_2922_: *mut crate::leanh::LeanObject,
    mut v_opt_2923_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2924_ = crate::leanh::lean_ctor_get(v_opt_2923_, 0);
    v_defValue_2925_ = crate::leanh::lean_ctor_get(v_opt_2923_, 1);
    v_map_2926_ = crate::leanh::lean_ctor_get(v_opts_2922_, 0);
    v___x_2927_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2926_,
            v_name_2924_,
        );
    if crate::leanh::lean_obj_tag(v___x_2927_) == 0 {
        let mut v___x_2928_: u8 = 0;
        v___x_2928_ = (crate::leanh::lean_unbox(v_defValue_2925_) as u8);
        return v___x_2928_;
    } else {
        let mut v_val_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2929_ = crate::leanh::lean_ctor_get(v___x_2927_, 0);
        crate::leanh::lean_inc(v_val_2929_);
        crate::leanh::lean_dec_ref_known(v___x_2927_, 1);
        if crate::leanh::lean_obj_tag(v_val_2929_) == 1 {
            let mut v_v_2930_: u8 = 0;
            v_v_2930_ = crate::leanh::lean_ctor_get_uint8(v_val_2929_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2929_, 0);
            return v_v_2930_;
        } else {
            let mut v___x_2931_: u8 = 0;
            crate::leanh::lean_dec(v_val_2929_);
            v___x_2931_ = (crate::leanh::lean_unbox(v_defValue_2925_) as u8);
            return v___x_2931_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(
    mut v_opts_2932_: *mut crate::leanh::LeanObject,
    mut v_opt_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2934_: u8 = 0;
    let mut v_r_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2934_ =
        l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_opts_2932_, v_opt_2933_);
    crate::leanh::lean_dec_ref(v_opt_2933_);
    crate::leanh::lean_dec_ref(v_opts_2932_);
    v_r_2935_ = crate::leanh::lean_box((v_res_2934_) as usize);
    return v_r_2935_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(
    mut v_a_2936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2937_ = lean_nat_to_int(v_a_2936_);
    return v___x_2937_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2946_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4;
    v___x_2947_ = lean_string_length(v___x_2946_);
    return v___x_2947_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2948_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once),
        _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6,
    );
    v___x_2949_ = lean_nat_to_int(v___x_2948_);
    return v___x_2949_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArg___redArg(
    mut v_e_2954_: *mut crate::leanh::LeanObject,
    mut v_a_2955_: *mut crate::leanh::LeanObject,
    mut v_a_2956_: *mut crate::leanh::LeanObject,
    mut v_a_2957_: *mut crate::leanh::LeanObject,
    mut v_a_2958_: *mut crate::leanh::LeanObject,
    mut v_a_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2968_: u8 = 0;
    let mut v_options_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: u8 = 0;
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: u8 = 0;
    let mut v___x_2979_: u8 = 0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2984_: u8 = 0;
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_2954_) {
                0 => {
                    v___x_2961_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1;
                    v___x_2962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2962_, 0, v___x_2961_);
                    return v___x_2962_;
                }
                1 => {
                    v_fvarId_2963_ = crate::leanh::lean_ctor_get(v_e_2954_, 0);
                    crate::leanh::lean_inc(v_fvarId_2963_);
                    crate::leanh::lean_dec_ref_known(v_e_2954_, 1);
                    v___x_2964_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_2963_,
                        v_a_2956_,
                        v_a_2957_,
                        v_a_2958_,
                        v_a_2959_,
                    );
                    return v___x_2964_;
                }
                _ => {
                    v_expr_2965_ = crate::leanh::lean_ctor_get(v_e_2954_, 0);
                    v_isSharedCheck_3001_ = (!crate::leanh::lean_is_exclusive(v_e_2954_)) as u8;
                    if v_isSharedCheck_3001_ == 0 {
                        v___x_2967_ = v_e_2954_;
                        v_isShared_2968_ = v_isSharedCheck_3001_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_expr_2965_);
                        crate::leanh::lean_dec(v_e_2954_);
                        v___x_2967_ = crate::leanh::lean_box(0);
                        v_isShared_2968_ = v_isSharedCheck_3001_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v_options_2969_ = crate::leanh::lean_ctor_get(v_a_2958_, 2);
                v___x_2970_ = l_Lean_pp_explicit;
                v___x_2971_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                    v_options_2969_,
                    v___x_2970_,
                );
                if v___x_2971_ == 0 {
                    crate::leanh::lean_dec_ref(v_expr_2965_);
                    v___x_2972_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3;
                    if v_isShared_2968_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2967_, 0);
                        crate::leanh::lean_ctor_set(v___x_2967_, 0, v___x_2972_);
                        v___x_2974_ = v___x_2967_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
                        v___x_2974_ = v_reuseFailAlloc_2975_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2967_);
                    v___x_2976_ = l_Lean_Expr_isConst(v_expr_2965_);
                    if v___x_2976_ == 0 {
                        v___x_2977_ = l_Lean_Expr_isProp(v_expr_2965_);
                        if v___x_2977_ == 0 {
                            v___x_2978_ = l_Lean_Expr_isType0(v_expr_2965_);
                            if v___x_2978_ == 0 {
                                v___x_2979_ = l_Lean_Expr_isFVar(v_expr_2965_);
                                if v___x_2979_ == 0 {
                                    v___x_2980_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                                        v_expr_2965_,
                                        v_a_2955_,
                                        v_a_2958_,
                                        v_a_2959_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2980_) == 0 {
                                        v_a_2981_ = crate::leanh::lean_ctor_get(v___x_2980_, 0);
                                        v_isSharedCheck_2996_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2980_)) as u8;
                                        if v_isSharedCheck_2996_ == 0 {
                                            v___x_2983_ = v___x_2980_;
                                            v_isShared_2984_ = v_isSharedCheck_2996_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2981_);
                                            crate::leanh::lean_dec(v___x_2980_);
                                            v___x_2983_ = crate::leanh::lean_box(0);
                                            v_isShared_2984_ = v_isSharedCheck_2996_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        return v___x_2980_;
                                    }
                                } else {
                                    v___x_2997_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                                        v_expr_2965_,
                                        v_a_2955_,
                                        v_a_2958_,
                                        v_a_2959_,
                                    );
                                    return v___x_2997_;
                                }
                            } else {
                                v___x_2998_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                                    v_expr_2965_,
                                    v_a_2955_,
                                    v_a_2958_,
                                    v_a_2959_,
                                );
                                return v___x_2998_;
                            }
                        } else {
                            v___x_2999_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                                v_expr_2965_,
                                v_a_2955_,
                                v_a_2958_,
                                v_a_2959_,
                            );
                            return v___x_2999_;
                        }
                    } else {
                        v___x_3000_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                            v_expr_2965_,
                            v_a_2955_,
                            v_a_2958_,
                            v_a_2959_,
                        );
                        return v___x_3000_;
                    }
                }
            }
            2 => {
                return v___x_2974_;
            }
            3 => {
                v___x_2985_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once
                    ),
                    _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7,
                );
                v___x_2986_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8;
                v___x_2987_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2987_, 0, v___x_2986_);
                crate::leanh::lean_ctor_set(v___x_2987_, 1, v_a_2981_);
                v___x_2988_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9;
                v___x_2989_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2989_, 0, v___x_2987_);
                crate::leanh::lean_ctor_set(v___x_2989_, 1, v___x_2988_);
                v___x_2990_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2990_, 0, v___x_2985_);
                crate::leanh::lean_ctor_set(v___x_2990_, 1, v___x_2989_);
                v___x_2991_ = 0;
                v___x_2992_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2992_, 0, v___x_2990_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2992_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2991_,
                );
                if v_isShared_2984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2983_, 0, v___x_2992_);
                    v___x_2994_ = v___x_2983_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2995_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
                    v___x_2994_ = v_reuseFailAlloc_2995_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(
    mut v_e_3002_: *mut crate::leanh::LeanObject,
    mut v_a_3003_: *mut crate::leanh::LeanObject,
    mut v_a_3004_: *mut crate::leanh::LeanObject,
    mut v_a_3005_: *mut crate::leanh::LeanObject,
    mut v_a_3006_: *mut crate::leanh::LeanObject,
    mut v_a_3007_: *mut crate::leanh::LeanObject,
    mut v_a_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3009_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(
        v_e_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_,
    );
    crate::leanh::lean_dec(v_a_3007_);
    crate::leanh::lean_dec_ref(v_a_3006_);
    crate::leanh::lean_dec(v_a_3005_);
    crate::leanh::lean_dec_ref(v_a_3004_);
    crate::leanh::lean_dec_ref(v_a_3003_);
    return v_res_3009_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArg(
    mut v_pu_3010_: u8,
    mut v_e_3011_: *mut crate::leanh::LeanObject,
    mut v_a_3012_: *mut crate::leanh::LeanObject,
    mut v_a_3013_: *mut crate::leanh::LeanObject,
    mut v_a_3014_: *mut crate::leanh::LeanObject,
    mut v_a_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3018_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(
        v_e_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_,
    );
    return v___x_3018_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArg___boxed(
    mut v_pu_3019_: *mut crate::leanh::LeanObject,
    mut v_e_3020_: *mut crate::leanh::LeanObject,
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v_a_3022_: *mut crate::leanh::LeanObject,
    mut v_a_3023_: *mut crate::leanh::LeanObject,
    mut v_a_3024_: *mut crate::leanh::LeanObject,
    mut v_a_3025_: *mut crate::leanh::LeanObject,
    mut v_a_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3027_: u8 = 0;
    let mut v_res_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3027_ = (crate::leanh::lean_unbox(v_pu_3019_) as u8);
    v_res_3028_ = l_Lean_Compiler_LCNF_PP_ppArg(
        v_pu_boxed_3027_,
        v_e_3020_,
        v_a_3021_,
        v_a_3022_,
        v_a_3023_,
        v_a_3024_,
        v_a_3025_,
    );
    crate::leanh::lean_dec(v_a_3025_);
    crate::leanh::lean_dec_ref(v_a_3024_);
    crate::leanh::lean_dec(v_a_3023_);
    crate::leanh::lean_dec_ref(v_a_3022_);
    crate::leanh::lean_dec_ref(v_a_3021_);
    return v_res_3028_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArgs(
    mut v_pu_3029_: u8,
    mut v_args_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
    mut v_a_3032_: *mut crate::leanh::LeanObject,
    mut v_a_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
    mut v_a_3035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3037_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
    v___x_3038_ = crate::leanh::lean_box((v_pu_3029_) as usize);
    v___x_3039_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PP_ppArg___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    crate::leanh::lean_closure_set(v___x_3039_, 0, v___x_3038_);
    v___x_3040_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(
            v___x_3037_,
            v_args_3030_,
            v___x_3039_,
            v_a_3031_,
            v_a_3032_,
            v_a_3033_,
            v_a_3034_,
            v_a_3035_,
        );
    return v___x_3040_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArgs___boxed(
    mut v_pu_3041_: *mut crate::leanh::LeanObject,
    mut v_args_3042_: *mut crate::leanh::LeanObject,
    mut v_a_3043_: *mut crate::leanh::LeanObject,
    mut v_a_3044_: *mut crate::leanh::LeanObject,
    mut v_a_3045_: *mut crate::leanh::LeanObject,
    mut v_a_3046_: *mut crate::leanh::LeanObject,
    mut v_a_3047_: *mut crate::leanh::LeanObject,
    mut v_a_3048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3049_: u8 = 0;
    let mut v_res_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3049_ = (crate::leanh::lean_unbox(v_pu_3041_) as u8);
    v_res_3050_ = l_Lean_Compiler_LCNF_PP_ppArgs(
        v_pu_boxed_3049_,
        v_args_3042_,
        v_a_3043_,
        v_a_3044_,
        v_a_3045_,
        v_a_3046_,
        v_a_3047_,
    );
    crate::leanh::lean_dec(v_a_3047_);
    crate::leanh::lean_dec_ref(v_a_3046_);
    crate::leanh::lean_dec(v_a_3045_);
    crate::leanh::lean_dec_ref(v_a_3044_);
    crate::leanh::lean_dec_ref(v_a_3043_);
    crate::leanh::lean_dec_ref(v_args_3042_);
    return v_res_3050_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(
    mut v_lit_3051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_3054_: u64 = 0;
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut v_val_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut v_val_3079_: u8 = 0;
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3084_: u16 = 0;
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3089_: u32 = 0;
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3094_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_lit_3051_) {
                0 => {
                    v_val_3059_ = crate::leanh::lean_ctor_get(v_lit_3051_, 0);
                    v_isSharedCheck_3068_ = (!crate::leanh::lean_is_exclusive(v_lit_3051_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v___x_3061_ = v_lit_3051_;
                        v_isShared_3062_ = v_isSharedCheck_3068_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3059_);
                        crate::leanh::lean_dec(v_lit_3051_);
                        v___x_3061_ = crate::leanh::lean_box(0);
                        v_isShared_3062_ = v_isSharedCheck_3068_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_val_3069_ = crate::leanh::lean_ctor_get(v_lit_3051_, 0);
                    v_isSharedCheck_3078_ = (!crate::leanh::lean_is_exclusive(v_lit_3051_)) as u8;
                    if v_isSharedCheck_3078_ == 0 {
                        v___x_3071_ = v_lit_3051_;
                        v_isShared_3072_ = v_isSharedCheck_3078_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3069_);
                        crate::leanh::lean_dec(v_lit_3051_);
                        v___x_3071_ = crate::leanh::lean_box(0);
                        v_isShared_3072_ = v_isSharedCheck_3078_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_val_3079_ = crate::leanh::lean_ctor_get_uint8(v_lit_3051_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_lit_3051_, 0);
                    v___x_3080_ = lean_uint8_to_nat(v_val_3079_);
                    v___x_3081_ = l_Nat_reprFast(v___x_3080_);
                    v___x_3082_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3082_, 0, v___x_3081_);
                    v___x_3083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3083_, 0, v___x_3082_);
                    return v___x_3083_;
                }
                3 => {
                    v_val_3084_ = crate::leanh::lean_ctor_get_uint16(v_lit_3051_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_lit_3051_, 0);
                    v___x_3085_ = lean_uint16_to_nat(v_val_3084_);
                    v___x_3086_ = l_Nat_reprFast(v___x_3085_);
                    v___x_3087_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3087_, 0, v___x_3086_);
                    v___x_3088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3088_, 0, v___x_3087_);
                    return v___x_3088_;
                }
                4 => {
                    v_val_3089_ = crate::leanh::lean_ctor_get_uint32(v_lit_3051_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_lit_3051_, 0);
                    v___x_3090_ = lean_uint32_to_nat(v_val_3089_);
                    v___x_3091_ = l_Nat_reprFast(v___x_3090_);
                    v___x_3092_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3092_, 0, v___x_3091_);
                    v___x_3093_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3093_, 0, v___x_3092_);
                    return v___x_3093_;
                }
                _ => {
                    v_val_3094_ = crate::leanh::lean_ctor_get_uint64(v_lit_3051_, 0 as u32);
                    crate::leanh::lean_dec_ref(v_lit_3051_);
                    v_v_3054_ = v_val_3094_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_3055_ = lean_uint64_to_nat(v_v_3054_);
                v___x_3056_ = l_Nat_reprFast(v___x_3055_);
                v___x_3057_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3057_, 0, v___x_3056_);
                v___x_3058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3058_, 0, v___x_3057_);
                return v___x_3058_;
            }
            2 => {
                v___x_3063_ = l_Nat_reprFast(v_val_3059_);
                if v_isShared_3062_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3061_, 3);
                    crate::leanh::lean_ctor_set(v___x_3061_, 0, v___x_3063_);
                    v___x_3065_ = v___x_3061_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3067_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3063_);
                    v___x_3065_ = v_reuseFailAlloc_3067_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3066_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3066_, 0, v___x_3065_);
                return v___x_3066_;
            }
            4 => {
                v___x_3073_ = l_String_quote(v_val_3069_);
                if v_isShared_3072_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3071_, 3);
                    crate::leanh::lean_ctor_set(v___x_3071_, 0, v___x_3073_);
                    v___x_3075_ = v___x_3071_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3077_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3073_);
                    v___x_3075_ = v_reuseFailAlloc_3077_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3076_, 0, v___x_3075_);
                return v___x_3076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(
    mut v_lit_3095_: *mut crate::leanh::LeanObject,
    mut v_a_3096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3097_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_3095_);
    return v_res_3097_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLitValue(
    mut v_lit_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
    mut v_a_3100_: *mut crate::leanh::LeanObject,
    mut v_a_3101_: *mut crate::leanh::LeanObject,
    mut v_a_3102_: *mut crate::leanh::LeanObject,
    mut v_a_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_3098_);
    return v___x_3105_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(
    mut v_lit_3106_: *mut crate::leanh::LeanObject,
    mut v_a_3107_: *mut crate::leanh::LeanObject,
    mut v_a_3108_: *mut crate::leanh::LeanObject,
    mut v_a_3109_: *mut crate::leanh::LeanObject,
    mut v_a_3110_: *mut crate::leanh::LeanObject,
    mut v_a_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3113_ = l_Lean_Compiler_LCNF_PP_ppLitValue(
        v_lit_3106_,
        v_a_3107_,
        v_a_3108_,
        v_a_3109_,
        v_a_3110_,
        v_a_3111_,
    );
    crate::leanh::lean_dec(v_a_3111_);
    crate::leanh::lean_dec_ref(v_a_3110_);
    crate::leanh::lean_dec(v_a_3109_);
    crate::leanh::lean_dec_ref(v_a_3108_);
    crate::leanh::lean_dec_ref(v_a_3107_);
    return v_res_3113_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(
    mut v_x_3126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3148_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: u8 = 0;
    let mut v___x_3160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3127_ = crate::leanh::lean_ctor_get(v_x_3126_, 0);
                crate::leanh::lean_inc(v_name_3127_);
                v_cidx_3128_ = crate::leanh::lean_ctor_get(v_x_3126_, 1);
                crate::leanh::lean_inc(v_cidx_3128_);
                v_usize_3129_ = crate::leanh::lean_ctor_get(v_x_3126_, 3);
                crate::leanh::lean_inc(v_usize_3129_);
                v_ssize_3130_ = crate::leanh::lean_ctor_get(v_x_3126_, 4);
                crate::leanh::lean_inc(v_ssize_3130_);
                crate::leanh::lean_dec_ref(v_x_3126_);
                v___x_3143_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5;
                v___x_3144_ = l_Nat_reprFast(v_cidx_3128_);
                v___x_3145_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3145_, 0, v___x_3144_);
                v_r_3146_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_r_3146_, 0, v___x_3143_);
                crate::leanh::lean_ctor_set(v_r_3146_, 1, v___x_3145_);
                v___x_3158_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3159_ = lean_nat_dec_lt(v___x_3158_, v_usize_3129_);
                if v___x_3159_ == 0 {
                    v___x_3160_ = lean_nat_dec_lt(v___x_3158_, v_ssize_3130_);
                    v___y_3148_ = v___x_3160_;
                    state = 2;
                    continue;
                } else {
                    v___y_3148_ = v___x_3159_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3133_ = crate::leanh::lean_box(0);
                v___x_3134_ = lean_name_eq(v_name_3127_, v___x_3133_);
                if v___x_3134_ == 0 {
                    v___x_3135_ = 1;
                    v___x_3136_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1;
                    v___x_3137_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3137_, 0, v_r_3132_);
                    crate::leanh::lean_ctor_set(v___x_3137_, 1, v___x_3136_);
                    v___x_3138_ = l_Lean_Name_toString(v_name_3127_, v___x_3135_);
                    v___x_3139_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3139_, 0, v___x_3138_);
                    v___x_3140_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3140_, 0, v___x_3137_);
                    crate::leanh::lean_ctor_set(v___x_3140_, 1, v___x_3139_);
                    v___x_3141_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3;
                    v_r_3142_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_r_3142_, 0, v___x_3140_);
                    crate::leanh::lean_ctor_set(v_r_3142_, 1, v___x_3141_);
                    return v_r_3142_;
                } else {
                    crate::leanh::lean_dec(v_name_3127_);
                    return v_r_3132_;
                }
            }
            2 => {
                if v___y_3148_ == 0 {
                    crate::leanh::lean_dec(v_ssize_3130_);
                    crate::leanh::lean_dec(v_usize_3129_);
                    v_r_3132_ = v_r_3146_;
                    state = 1;
                    continue;
                } else {
                    v___x_3149_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7;
                    v___x_3150_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3150_, 0, v_r_3146_);
                    crate::leanh::lean_ctor_set(v___x_3150_, 1, v___x_3149_);
                    v___x_3151_ = l_Nat_reprFast(v_usize_3129_);
                    v___x_3152_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3152_, 0, v___x_3151_);
                    v___x_3153_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3153_, 0, v___x_3150_);
                    crate::leanh::lean_ctor_set(v___x_3153_, 1, v___x_3152_);
                    v___x_3154_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3154_, 0, v___x_3153_);
                    crate::leanh::lean_ctor_set(v___x_3154_, 1, v___x_3149_);
                    v___x_3155_ = l_Nat_reprFast(v_ssize_3130_);
                    v___x_3156_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
                    v_r_3157_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_r_3157_, 0, v___x_3154_);
                    crate::leanh::lean_ctor_set(v_r_3157_, 1, v___x_3156_);
                    v_r_3132_ = v_r_3157_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(
    mut v_a_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3162_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(
            v_a_3161_,
        );
    return v___x_3162_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLetValue(
    mut v_pu_3210_: u8,
    mut v_e_3211_: *mut crate::leanh::LeanObject,
    mut v_a_3212_: *mut crate::leanh::LeanObject,
    mut v_a_3213_: *mut crate::leanh::LeanObject,
    mut v_a_3214_: *mut crate::leanh::LeanObject,
    mut v_a_3215_: *mut crate::leanh::LeanObject,
    mut v_a_3216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_value_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3228_: u8 = 0;
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut v_declName_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut v_fvarId_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_i_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_i_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3297_: u8 = 0;
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3302_: u8 = 0;
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3315_: u8 = 0;
    let mut v_isSharedCheck_3316_: u8 = 0;
    let mut v_i_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3321_: u8 = 0;
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3339_: u8 = 0;
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v_n_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_fn_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_isSharedCheck_3385_: u8 = 0;
    let mut v_fn_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3390_: u8 = 0;
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3395_: u8 = 0;
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3407_: u8 = 0;
    let mut v_isSharedCheck_3408_: u8 = 0;
    let mut v_n_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3418_: u8 = 0;
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3431_: u8 = 0;
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut v_var_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_3435_: u8 = 0;
    let mut v_args_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3461_: u8 = 0;
    let mut v_fvarId_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3470_: u8 = 0;
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v_isSharedCheck_3479_: u8 = 0;
    let mut v_unused_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3492_: u8 = 0;
    let mut v_fvarId_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_3211_) {
                0 => {
                    v_value_3218_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    crate::leanh::lean_inc_ref(v_value_3218_);
                    crate::leanh::lean_dec_ref_known(v_e_3211_, 1);
                    v___x_3219_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_value_3218_);
                    return v___x_3219_;
                }
                1 => {
                    v___x_3220_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1;
                    v___x_3221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3221_, 0, v___x_3220_);
                    return v___x_3221_;
                }
                2 => {
                    v_idx_3222_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    crate::leanh::lean_inc(v_idx_3222_);
                    v_struct_3223_ = crate::leanh::lean_ctor_get(v_e_3211_, 2);
                    crate::leanh::lean_inc(v_struct_3223_);
                    crate::leanh::lean_dec_ref_known(v_e_3211_, 3);
                    v___x_3224_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_struct_3223_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3224_) == 0 {
                        v_a_3225_ = crate::leanh::lean_ctor_get(v___x_3224_, 0);
                        v_isSharedCheck_3237_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3224_)) as u8;
                        if v_isSharedCheck_3237_ == 0 {
                            v___x_3227_ = v___x_3224_;
                            v_isShared_3228_ = v_isSharedCheck_3237_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3225_);
                            crate::leanh::lean_dec(v___x_3224_);
                            v___x_3227_ = crate::leanh::lean_box(0);
                            v_isShared_3228_ = v_isSharedCheck_3237_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_idx_3222_);
                        return v___x_3224_;
                    }
                }
                3 => {
                    v_declName_3238_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    crate::leanh::lean_inc(v_declName_3238_);
                    v_us_3239_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    crate::leanh::lean_inc(v_us_3239_);
                    v_args_3240_ = crate::leanh::lean_ctor_get(v_e_3211_, 2);
                    crate::leanh::lean_inc_ref(v_args_3240_);
                    crate::leanh::lean_dec_ref_known(v_e_3211_, 3);
                    v___x_3241_ = l_Lean_Expr_const___override(v_declName_3238_, v_us_3239_);
                    v___x_3242_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                        v___x_3241_,
                        v_a_3212_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3242_) == 0 {
                        v_a_3243_ = crate::leanh::lean_ctor_get(v___x_3242_, 0);
                        crate::leanh::lean_inc(v_a_3243_);
                        crate::leanh::lean_dec_ref_known(v___x_3242_, 1);
                        v___x_3244_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                            v_pu_3210_,
                            v_args_3240_,
                            v_a_3212_,
                            v_a_3213_,
                            v_a_3214_,
                            v_a_3215_,
                            v_a_3216_,
                        );
                        crate::leanh::lean_dec_ref(v_args_3240_);
                        if crate::leanh::lean_obj_tag(v___x_3244_) == 0 {
                            v_a_3245_ = crate::leanh::lean_ctor_get(v___x_3244_, 0);
                            v_isSharedCheck_3253_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3244_)) as u8;
                            if v_isSharedCheck_3253_ == 0 {
                                v___x_3247_ = v___x_3244_;
                                v_isShared_3248_ = v_isSharedCheck_3253_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3245_);
                                crate::leanh::lean_dec(v___x_3244_);
                                v___x_3247_ = crate::leanh::lean_box(0);
                                v_isShared_3248_ = v_isSharedCheck_3253_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3243_);
                            return v___x_3244_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_3240_);
                        return v___x_3242_;
                    }
                }
                4 => {
                    v_fvarId_3254_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    v_args_3255_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3273_ = (!crate::leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3273_ == 0 {
                        v___x_3257_ = v_e_3211_;
                        v_isShared_3258_ = v_isSharedCheck_3273_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_3255_);
                        crate::leanh::lean_inc(v_fvarId_3254_);
                        crate::leanh::lean_dec(v_e_3211_);
                        v___x_3257_ = crate::leanh::lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3273_;
                        state = 5;
                        continue;
                    }
                }
                5 => {
                    v_i_3274_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    v_args_3275_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3292_ = (!crate::leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3292_ == 0 {
                        v___x_3277_ = v_e_3211_;
                        v_isShared_3278_ = v_isSharedCheck_3292_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_3275_);
                        crate::leanh::lean_inc(v_i_3274_);
                        crate::leanh::lean_dec(v_e_3211_);
                        v___x_3277_ = crate::leanh::lean_box(0);
                        v_isShared_3278_ = v_isSharedCheck_3292_;
                        state = 9;
                        continue;
                    }
                }
                6 => {
                    v_i_3293_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    v_var_3294_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3316_ = (!crate::leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3316_ == 0 {
                        v___x_3296_ = v_e_3211_;
                        v_isShared_3297_ = v_isSharedCheck_3316_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_var_3294_);
                        crate::leanh::lean_inc(v_i_3293_);
                        crate::leanh::lean_dec(v_e_3211_);
                        v___x_3296_ = crate::leanh::lean_box(0);
                        v_isShared_3297_ = v_isSharedCheck_3316_;
                        state = 13;
                        continue;
                    }
                }
                7 => {
                    v_i_3317_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    v_var_3318_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3340_ = (!crate::leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3340_ == 0 {
                        v___x_3320_ = v_e_3211_;
                        v_isShared_3321_ = v_isSharedCheck_3340_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_var_3318_);
                        crate::leanh::lean_inc(v_i_3317_);
                        crate::leanh::lean_dec(v_e_3211_);
                        v___x_3320_ = crate::leanh::lean_box(0);
                        v_isShared_3321_ = v_isSharedCheck_3340_;
                        state = 17;
                        continue;
                    }
                }
                8 => {
                    v_n_3341_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    crate::leanh::lean_inc(v_n_3341_);
                    v_offset_3342_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    crate::leanh::lean_inc(v_offset_3342_);
                    v_var_3343_ = crate::leanh::lean_ctor_get(v_e_3211_, 2);
                    crate::leanh::lean_inc(v_var_3343_);
                    crate::leanh::lean_dec_ref_known(v_e_3211_, 3);
                    v___x_3344_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_var_3343_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3344_) == 0 {
                        v_a_3345_ = crate::leanh::lean_ctor_get(v___x_3344_, 0);
                        v_isSharedCheck_3364_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3344_)) as u8;
                        if v_isSharedCheck_3364_ == 0 {
                            v___x_3347_ = v___x_3344_;
                            v_isShared_3348_ = v_isSharedCheck_3364_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3345_);
                            crate::leanh::lean_dec(v___x_3344_);
                            v___x_3347_ = crate::leanh::lean_box(0);
                            v_isShared_3348_ = v_isSharedCheck_3364_;
                            state = 21;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_offset_3342_);
                        crate::leanh::lean_dec(v_n_3341_);
                        return v___x_3344_;
                    }
                }
                9 => {
                    v_fn_3365_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    v_args_3366_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3385_ = (!crate::leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3385_ == 0 {
                        v___x_3368_ = v_e_3211_;
                        v_isShared_3369_ = v_isSharedCheck_3385_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_3366_);
                        crate::leanh::lean_inc(v_fn_3365_);
                        crate::leanh::lean_dec(v_e_3211_);
                        v___x_3368_ = crate::leanh::lean_box(0);
                        v_isShared_3369_ = v_isSharedCheck_3385_;
                        state = 23;
                        continue;
                    }
                }
                10 => {
                    v_fn_3386_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    v_args_3387_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3408_ = (!crate::leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3408_ == 0 {
                        v___x_3389_ = v_e_3211_;
                        v_isShared_3390_ = v_isSharedCheck_3408_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_3387_);
                        crate::leanh::lean_inc(v_fn_3386_);
                        crate::leanh::lean_dec(v_e_3211_);
                        v___x_3389_ = crate::leanh::lean_box(0);
                        v_isShared_3390_ = v_isSharedCheck_3408_;
                        state = 27;
                        continue;
                    }
                }
                11 => {
                    v_n_3409_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    v_var_3410_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3432_ = (!crate::leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3432_ == 0 {
                        v___x_3412_ = v_e_3211_;
                        v_isShared_3413_ = v_isSharedCheck_3432_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_var_3410_);
                        crate::leanh::lean_inc(v_n_3409_);
                        crate::leanh::lean_dec(v_e_3211_);
                        v___x_3412_ = crate::leanh::lean_box(0);
                        v_isShared_3413_ = v_isSharedCheck_3432_;
                        state = 31;
                        continue;
                    }
                }
                12 => {
                    v_var_3433_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    crate::leanh::lean_inc(v_var_3433_);
                    v_i_3434_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    crate::leanh::lean_inc_ref(v_i_3434_);
                    v_updateHeader_3435_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3211_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_args_3436_ = crate::leanh::lean_ctor_get(v_e_3211_, 2);
                    crate::leanh::lean_inc_ref(v_args_3436_);
                    crate::leanh::lean_dec_ref_known(v_e_3211_, 3);
                    v___x_3437_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_var_3433_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3437_) == 0 {
                        v_a_3438_ = crate::leanh::lean_ctor_get(v___x_3437_, 0);
                        crate::leanh::lean_inc(v_a_3438_);
                        crate::leanh::lean_dec_ref_known(v___x_3437_, 1);
                        v___x_3439_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                            v_pu_3210_,
                            v_args_3436_,
                            v_a_3212_,
                            v_a_3213_,
                            v_a_3214_,
                            v_a_3215_,
                            v_a_3216_,
                        );
                        crate::leanh::lean_dec_ref(v_args_3436_);
                        if crate::leanh::lean_obj_tag(v___x_3439_) == 0 {
                            v_a_3440_ = crate::leanh::lean_ctor_get(v___x_3439_, 0);
                            v_isSharedCheck_3461_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3439_)) as u8;
                            if v_isSharedCheck_3461_ == 0 {
                                v___x_3442_ = v___x_3439_;
                                v_isShared_3443_ = v_isSharedCheck_3461_;
                                state = 35;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3440_);
                                crate::leanh::lean_dec(v___x_3439_);
                                v___x_3442_ = crate::leanh::lean_box(0);
                                v_isShared_3443_ = v_isSharedCheck_3461_;
                                state = 35;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3438_);
                            crate::leanh::lean_dec_ref(v_i_3434_);
                            return v___x_3439_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_3436_);
                        crate::leanh::lean_dec_ref(v_i_3434_);
                        return v___x_3437_;
                    }
                }
                13 => {
                    v_fvarId_3462_ = crate::leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3479_ = (!crate::leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3479_ == 0 {
                        v_unused_3480_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                        crate::leanh::lean_dec(v_unused_3480_);
                        v___x_3464_ = v_e_3211_;
                        v_isShared_3465_ = v_isSharedCheck_3479_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_3462_);
                        crate::leanh::lean_dec(v_e_3211_);
                        v___x_3464_ = crate::leanh::lean_box(0);
                        v_isShared_3465_ = v_isSharedCheck_3479_;
                        state = 38;
                        continue;
                    }
                }
                14 => {
                    v_fvarId_3481_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    crate::leanh::lean_inc(v_fvarId_3481_);
                    crate::leanh::lean_dec_ref_known(v_e_3211_, 1);
                    v___x_3482_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_3481_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3482_) == 0 {
                        v_a_3483_ = crate::leanh::lean_ctor_get(v___x_3482_, 0);
                        v_isSharedCheck_3492_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3482_)) as u8;
                        if v_isSharedCheck_3492_ == 0 {
                            v___x_3485_ = v___x_3482_;
                            v_isShared_3486_ = v_isSharedCheck_3492_;
                            state = 42;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3483_);
                            crate::leanh::lean_dec(v___x_3482_);
                            v___x_3485_ = crate::leanh::lean_box(0);
                            v_isShared_3486_ = v_isSharedCheck_3492_;
                            state = 42;
                            continue;
                        }
                    } else {
                        return v___x_3482_;
                    }
                }
                _ => {
                    v_fvarId_3493_ = crate::leanh::lean_ctor_get(v_e_3211_, 0);
                    crate::leanh::lean_inc(v_fvarId_3493_);
                    crate::leanh::lean_dec_ref_known(v_e_3211_, 1);
                    v___x_3494_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_3493_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3494_) == 0 {
                        v_a_3495_ = crate::leanh::lean_ctor_get(v___x_3494_, 0);
                        v_isSharedCheck_3504_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3494_)) as u8;
                        if v_isSharedCheck_3504_ == 0 {
                            v___x_3497_ = v___x_3494_;
                            v_isShared_3498_ = v_isSharedCheck_3504_;
                            state = 44;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3495_);
                            crate::leanh::lean_dec(v___x_3494_);
                            v___x_3497_ = crate::leanh::lean_box(0);
                            v_isShared_3498_ = v_isSharedCheck_3504_;
                            state = 44;
                            continue;
                        }
                    } else {
                        return v___x_3494_;
                    }
                }
            },
            1 => {
                v___x_3229_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1;
                v___x_3230_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3230_, 0, v_a_3225_);
                crate::leanh::lean_ctor_set(v___x_3230_, 1, v___x_3229_);
                v___x_3231_ = l_Nat_reprFast(v_idx_3222_);
                v___x_3232_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3232_, 0, v___x_3231_);
                v___x_3233_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3233_, 0, v___x_3230_);
                crate::leanh::lean_ctor_set(v___x_3233_, 1, v___x_3232_);
                if v_isShared_3228_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3227_, 0, v___x_3233_);
                    v___x_3235_ = v___x_3227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
                    v___x_3235_ = v_reuseFailAlloc_3236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3235_;
            }
            3 => {
                v___x_3249_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3249_, 0, v_a_3243_);
                crate::leanh::lean_ctor_set(v___x_3249_, 1, v_a_3245_);
                if v_isShared_3248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3247_, 0, v___x_3249_);
                    v___x_3251_ = v___x_3247_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
                    v___x_3251_ = v_reuseFailAlloc_3252_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3251_;
            }
            5 => {
                v___x_3259_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                    v_fvarId_3254_,
                    v_a_3213_,
                    v_a_3214_,
                    v_a_3215_,
                    v_a_3216_,
                );
                if crate::leanh::lean_obj_tag(v___x_3259_) == 0 {
                    v_a_3260_ = crate::leanh::lean_ctor_get(v___x_3259_, 0);
                    crate::leanh::lean_inc(v_a_3260_);
                    crate::leanh::lean_dec_ref_known(v___x_3259_, 1);
                    v___x_3261_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                        v_pu_3210_,
                        v_args_3255_,
                        v_a_3212_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    crate::leanh::lean_dec_ref(v_args_3255_);
                    if crate::leanh::lean_obj_tag(v___x_3261_) == 0 {
                        v_a_3262_ = crate::leanh::lean_ctor_get(v___x_3261_, 0);
                        v_isSharedCheck_3272_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3261_)) as u8;
                        if v_isSharedCheck_3272_ == 0 {
                            v___x_3264_ = v___x_3261_;
                            v_isShared_3265_ = v_isSharedCheck_3272_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3262_);
                            crate::leanh::lean_dec(v___x_3261_);
                            v___x_3264_ = crate::leanh::lean_box(0);
                            v_isShared_3265_ = v_isSharedCheck_3272_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3260_);
                        crate::leanh::lean_del_object(v___x_3257_);
                        return v___x_3261_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3257_);
                    crate::leanh::lean_dec_ref(v_args_3255_);
                    return v___x_3259_;
                }
            }
            6 => {
                if v_isShared_3258_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3257_, 5);
                    crate::leanh::lean_ctor_set(v___x_3257_, 1, v_a_3262_);
                    crate::leanh::lean_ctor_set(v___x_3257_, 0, v_a_3260_);
                    v___x_3267_ = v___x_3257_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3271_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3260_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_a_3262_);
                    v___x_3267_ = v_reuseFailAlloc_3271_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3264_, 0, v___x_3267_);
                    v___x_3269_ = v___x_3264_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
                    v___x_3269_ = v_reuseFailAlloc_3270_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3269_;
            }
            9 => {
                v___x_3279_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                    v_pu_3210_,
                    v_args_3275_,
                    v_a_3212_,
                    v_a_3213_,
                    v_a_3214_,
                    v_a_3215_,
                    v_a_3216_,
                );
                crate::leanh::lean_dec_ref(v_args_3275_);
                if crate::leanh::lean_obj_tag(v___x_3279_) == 0 {
                    v_a_3280_ = crate::leanh::lean_ctor_get(v___x_3279_, 0);
                    v_isSharedCheck_3291_ = (!crate::leanh::lean_is_exclusive(v___x_3279_)) as u8;
                    if v_isSharedCheck_3291_ == 0 {
                        v___x_3282_ = v___x_3279_;
                        v_isShared_3283_ = v_isSharedCheck_3291_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3280_);
                        crate::leanh::lean_dec(v___x_3279_);
                        v___x_3282_ = crate::leanh::lean_box(0);
                        v_isShared_3283_ = v_isSharedCheck_3291_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3277_);
                    crate::leanh::lean_dec_ref(v_i_3274_);
                    return v___x_3279_;
                }
            }
            10 => {
                v___x_3284_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_3274_);
                if v_isShared_3278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3277_, 1, v_a_3280_);
                    crate::leanh::lean_ctor_set(v___x_3277_, 0, v___x_3284_);
                    v___x_3286_ = v___x_3277_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_a_3280_);
                    v___x_3286_ = v_reuseFailAlloc_3290_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3282_, 0, v___x_3286_);
                    v___x_3288_ = v___x_3282_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3288_;
            }
            13 => {
                v___x_3298_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                    v_var_3294_,
                    v_a_3213_,
                    v_a_3214_,
                    v_a_3215_,
                    v_a_3216_,
                );
                if crate::leanh::lean_obj_tag(v___x_3298_) == 0 {
                    v_a_3299_ = crate::leanh::lean_ctor_get(v___x_3298_, 0);
                    v_isSharedCheck_3315_ = (!crate::leanh::lean_is_exclusive(v___x_3298_)) as u8;
                    if v_isSharedCheck_3315_ == 0 {
                        v___x_3301_ = v___x_3298_;
                        v_isShared_3302_ = v_isSharedCheck_3315_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3299_);
                        crate::leanh::lean_dec(v___x_3298_);
                        v___x_3301_ = crate::leanh::lean_box(0);
                        v_isShared_3302_ = v_isSharedCheck_3315_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3296_);
                    crate::leanh::lean_dec(v_i_3293_);
                    return v___x_3298_;
                }
            }
            14 => {
                v___x_3303_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3;
                v___x_3304_ = l_Nat_reprFast(v_i_3293_);
                v___x_3305_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3305_, 0, v___x_3304_);
                if v_isShared_3297_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3296_, 5);
                    crate::leanh::lean_ctor_set(v___x_3296_, 1, v___x_3305_);
                    crate::leanh::lean_ctor_set(v___x_3296_, 0, v___x_3303_);
                    v___x_3307_ = v___x_3296_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3314_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___x_3305_);
                    v___x_3307_ = v_reuseFailAlloc_3314_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3308_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5;
                v___x_3309_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3309_, 0, v___x_3307_);
                crate::leanh::lean_ctor_set(v___x_3309_, 1, v___x_3308_);
                v___x_3310_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3310_, 0, v___x_3309_);
                crate::leanh::lean_ctor_set(v___x_3310_, 1, v_a_3299_);
                if v_isShared_3302_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3301_, 0, v___x_3310_);
                    v___x_3312_ = v___x_3301_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
                    v___x_3312_ = v_reuseFailAlloc_3313_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3312_;
            }
            17 => {
                v___x_3322_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                    v_var_3318_,
                    v_a_3213_,
                    v_a_3214_,
                    v_a_3215_,
                    v_a_3216_,
                );
                if crate::leanh::lean_obj_tag(v___x_3322_) == 0 {
                    v_a_3323_ = crate::leanh::lean_ctor_get(v___x_3322_, 0);
                    v_isSharedCheck_3339_ = (!crate::leanh::lean_is_exclusive(v___x_3322_)) as u8;
                    if v_isSharedCheck_3339_ == 0 {
                        v___x_3325_ = v___x_3322_;
                        v_isShared_3326_ = v_isSharedCheck_3339_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3323_);
                        crate::leanh::lean_dec(v___x_3322_);
                        v___x_3325_ = crate::leanh::lean_box(0);
                        v_isShared_3326_ = v_isSharedCheck_3339_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3320_);
                    crate::leanh::lean_dec(v_i_3317_);
                    return v___x_3322_;
                }
            }
            18 => {
                v___x_3327_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7;
                v___x_3328_ = l_Nat_reprFast(v_i_3317_);
                v___x_3329_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3329_, 0, v___x_3328_);
                if v_isShared_3321_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3320_, 5);
                    crate::leanh::lean_ctor_set(v___x_3320_, 1, v___x_3329_);
                    crate::leanh::lean_ctor_set(v___x_3320_, 0, v___x_3327_);
                    v___x_3331_ = v___x_3320_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3338_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3338_, 1, v___x_3329_);
                    v___x_3331_ = v_reuseFailAlloc_3338_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_3332_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5;
                v___x_3333_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3333_, 0, v___x_3331_);
                crate::leanh::lean_ctor_set(v___x_3333_, 1, v___x_3332_);
                v___x_3334_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3334_, 0, v___x_3333_);
                crate::leanh::lean_ctor_set(v___x_3334_, 1, v_a_3323_);
                if v_isShared_3326_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3325_, 0, v___x_3334_);
                    v___x_3336_ = v___x_3325_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3337_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
                    v___x_3336_ = v_reuseFailAlloc_3337_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3336_;
            }
            21 => {
                v___x_3349_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9;
                v___x_3350_ = l_Nat_reprFast(v_n_3341_);
                v___x_3351_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3351_, 0, v___x_3350_);
                v___x_3352_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3349_);
                crate::leanh::lean_ctor_set(v___x_3352_, 1, v___x_3351_);
                v___x_3353_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11;
                v___x_3354_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3354_, 0, v___x_3352_);
                crate::leanh::lean_ctor_set(v___x_3354_, 1, v___x_3353_);
                v___x_3355_ = l_Nat_reprFast(v_offset_3342_);
                v___x_3356_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3356_, 0, v___x_3355_);
                v___x_3357_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3357_, 0, v___x_3354_);
                crate::leanh::lean_ctor_set(v___x_3357_, 1, v___x_3356_);
                v___x_3358_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5;
                v___x_3359_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3359_, 0, v___x_3357_);
                crate::leanh::lean_ctor_set(v___x_3359_, 1, v___x_3358_);
                v___x_3360_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3360_, 0, v___x_3359_);
                crate::leanh::lean_ctor_set(v___x_3360_, 1, v_a_3345_);
                if v_isShared_3348_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3347_, 0, v___x_3360_);
                    v___x_3362_ = v___x_3347_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3363_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
                    v___x_3362_ = v_reuseFailAlloc_3363_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3362_;
            }
            23 => {
                v___x_3370_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                    v_pu_3210_,
                    v_args_3366_,
                    v_a_3212_,
                    v_a_3213_,
                    v_a_3214_,
                    v_a_3215_,
                    v_a_3216_,
                );
                crate::leanh::lean_dec_ref(v_args_3366_);
                if crate::leanh::lean_obj_tag(v___x_3370_) == 0 {
                    v_a_3371_ = crate::leanh::lean_ctor_get(v___x_3370_, 0);
                    v_isSharedCheck_3384_ = (!crate::leanh::lean_is_exclusive(v___x_3370_)) as u8;
                    if v_isSharedCheck_3384_ == 0 {
                        v___x_3373_ = v___x_3370_;
                        v_isShared_3374_ = v_isSharedCheck_3384_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3371_);
                        crate::leanh::lean_dec(v___x_3370_);
                        v___x_3373_ = crate::leanh::lean_box(0);
                        v_isShared_3374_ = v_isSharedCheck_3384_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3368_);
                    crate::leanh::lean_dec(v_fn_3365_);
                    return v___x_3370_;
                }
            }
            24 => {
                v___x_3375_ = 1;
                v___x_3376_ = l_Lean_Name_toString(v_fn_3365_, v___x_3375_);
                v___x_3377_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3377_, 0, v___x_3376_);
                if v_isShared_3369_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3368_, 5);
                    crate::leanh::lean_ctor_set(v___x_3368_, 1, v_a_3371_);
                    crate::leanh::lean_ctor_set(v___x_3368_, 0, v___x_3377_);
                    v___x_3379_ = v___x_3368_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_a_3371_);
                    v___x_3379_ = v_reuseFailAlloc_3383_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_3374_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3373_, 0, v___x_3379_);
                    v___x_3381_ = v___x_3373_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
                    v___x_3381_ = v_reuseFailAlloc_3382_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3381_;
            }
            27 => {
                v___x_3391_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                    v_pu_3210_,
                    v_args_3387_,
                    v_a_3212_,
                    v_a_3213_,
                    v_a_3214_,
                    v_a_3215_,
                    v_a_3216_,
                );
                crate::leanh::lean_dec_ref(v_args_3387_);
                if crate::leanh::lean_obj_tag(v___x_3391_) == 0 {
                    v_a_3392_ = crate::leanh::lean_ctor_get(v___x_3391_, 0);
                    v_isSharedCheck_3407_ = (!crate::leanh::lean_is_exclusive(v___x_3391_)) as u8;
                    if v_isSharedCheck_3407_ == 0 {
                        v___x_3394_ = v___x_3391_;
                        v_isShared_3395_ = v_isSharedCheck_3407_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3392_);
                        crate::leanh::lean_dec(v___x_3391_);
                        v___x_3394_ = crate::leanh::lean_box(0);
                        v_isShared_3395_ = v_isSharedCheck_3407_;
                        state = 28;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3389_);
                    crate::leanh::lean_dec(v_fn_3386_);
                    return v___x_3391_;
                }
            }
            28 => {
                v___x_3396_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13;
                v___x_3397_ = 1;
                v___x_3398_ = l_Lean_Name_toString(v_fn_3386_, v___x_3397_);
                v___x_3399_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3399_, 0, v___x_3398_);
                if v_isShared_3390_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3389_, 5);
                    crate::leanh::lean_ctor_set(v___x_3389_, 1, v___x_3399_);
                    crate::leanh::lean_ctor_set(v___x_3389_, 0, v___x_3396_);
                    v___x_3401_ = v___x_3389_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3406_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3406_, 1, v___x_3399_);
                    v___x_3401_ = v_reuseFailAlloc_3406_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_3402_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3402_, 0, v___x_3401_);
                crate::leanh::lean_ctor_set(v___x_3402_, 1, v_a_3392_);
                if v_isShared_3395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3394_, 0, v___x_3402_);
                    v___x_3404_ = v___x_3394_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
                    v___x_3404_ = v_reuseFailAlloc_3405_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3404_;
            }
            31 => {
                v___x_3414_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                    v_var_3410_,
                    v_a_3213_,
                    v_a_3214_,
                    v_a_3215_,
                    v_a_3216_,
                );
                if crate::leanh::lean_obj_tag(v___x_3414_) == 0 {
                    v_a_3415_ = crate::leanh::lean_ctor_get(v___x_3414_, 0);
                    v_isSharedCheck_3431_ = (!crate::leanh::lean_is_exclusive(v___x_3414_)) as u8;
                    if v_isSharedCheck_3431_ == 0 {
                        v___x_3417_ = v___x_3414_;
                        v_isShared_3418_ = v_isSharedCheck_3431_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3415_);
                        crate::leanh::lean_dec(v___x_3414_);
                        v___x_3417_ = crate::leanh::lean_box(0);
                        v_isShared_3418_ = v_isSharedCheck_3431_;
                        state = 32;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3412_);
                    crate::leanh::lean_dec(v_n_3409_);
                    return v___x_3414_;
                }
            }
            32 => {
                v___x_3419_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15;
                v___x_3420_ = l_Nat_reprFast(v_n_3409_);
                v___x_3421_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3421_, 0, v___x_3420_);
                if v_isShared_3413_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3412_, 5);
                    crate::leanh::lean_ctor_set(v___x_3412_, 1, v___x_3421_);
                    crate::leanh::lean_ctor_set(v___x_3412_, 0, v___x_3419_);
                    v___x_3423_ = v___x_3412_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3430_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3421_);
                    v___x_3423_ = v_reuseFailAlloc_3430_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_3424_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5;
                v___x_3425_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3425_, 0, v___x_3423_);
                crate::leanh::lean_ctor_set(v___x_3425_, 1, v___x_3424_);
                v___x_3426_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3426_, 0, v___x_3425_);
                crate::leanh::lean_ctor_set(v___x_3426_, 1, v_a_3415_);
                if v_isShared_3418_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3417_, 0, v___x_3426_);
                    v___x_3428_ = v___x_3417_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
                    v___x_3428_ = v_reuseFailAlloc_3429_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3428_;
            }
            35 => {
                v___x_3444_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17;
                if v_updateHeader_3435_ == 0 {
                    v___x_3459_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21;
                    v___y_3446_ = v___x_3459_;
                    state = 36;
                    continue;
                } else {
                    v___x_3460_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23;
                    v___y_3446_ = v___x_3460_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v___y_3446_);
                v___x_3447_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3447_, 0, v___x_3444_);
                crate::leanh::lean_ctor_set(v___x_3447_, 1, v___y_3446_);
                v___x_3448_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_3449_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3449_, 0, v___x_3448_);
                crate::leanh::lean_ctor_set(v___x_3449_, 1, v_a_3438_);
                v___x_3450_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19;
                v___x_3451_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3451_, 0, v___x_3449_);
                crate::leanh::lean_ctor_set(v___x_3451_, 1, v___x_3450_);
                v___x_3452_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_3434_);
                v___x_3453_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3453_, 0, v___x_3451_);
                crate::leanh::lean_ctor_set(v___x_3453_, 1, v___x_3452_);
                v___x_3454_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3454_, 0, v___x_3453_);
                crate::leanh::lean_ctor_set(v___x_3454_, 1, v_a_3440_);
                v___x_3455_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3455_, 0, v___x_3447_);
                crate::leanh::lean_ctor_set(v___x_3455_, 1, v___x_3454_);
                if v_isShared_3443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3442_, 0, v___x_3455_);
                    v___x_3457_ = v___x_3442_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
                    v___x_3457_ = v_reuseFailAlloc_3458_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3457_;
            }
            38 => {
                v___x_3466_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                    v_fvarId_3462_,
                    v_a_3213_,
                    v_a_3214_,
                    v_a_3215_,
                    v_a_3216_,
                );
                if crate::leanh::lean_obj_tag(v___x_3466_) == 0 {
                    v_a_3467_ = crate::leanh::lean_ctor_get(v___x_3466_, 0);
                    v_isSharedCheck_3478_ = (!crate::leanh::lean_is_exclusive(v___x_3466_)) as u8;
                    if v_isSharedCheck_3478_ == 0 {
                        v___x_3469_ = v___x_3466_;
                        v_isShared_3470_ = v_isSharedCheck_3478_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3467_);
                        crate::leanh::lean_dec(v___x_3466_);
                        v___x_3469_ = crate::leanh::lean_box(0);
                        v_isShared_3470_ = v_isSharedCheck_3478_;
                        state = 39;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3464_);
                    return v___x_3466_;
                }
            }
            39 => {
                v___x_3471_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25;
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3464_, 5);
                    crate::leanh::lean_ctor_set(v___x_3464_, 1, v_a_3467_);
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3471_);
                    v___x_3473_ = v___x_3464_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_a_3467_);
                    v___x_3473_ = v_reuseFailAlloc_3477_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3470_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3469_, 0, v___x_3473_);
                    v___x_3475_ = v___x_3469_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
                    v___x_3475_ = v_reuseFailAlloc_3476_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3475_;
            }
            42 => {
                v___x_3487_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27;
                v___x_3488_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3488_, 0, v___x_3487_);
                crate::leanh::lean_ctor_set(v___x_3488_, 1, v_a_3483_);
                if v_isShared_3486_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3485_, 0, v___x_3488_);
                    v___x_3490_ = v___x_3485_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
                    v___x_3490_ = v_reuseFailAlloc_3491_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_3490_;
            }
            44 => {
                v___x_3499_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29;
                v___x_3500_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3500_, 0, v___x_3499_);
                crate::leanh::lean_ctor_set(v___x_3500_, 1, v_a_3495_);
                if v_isShared_3498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3497_, 0, v___x_3500_);
                    v___x_3502_ = v___x_3497_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
                    v___x_3502_ = v_reuseFailAlloc_3503_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_3502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(
    mut v_pu_3505_: *mut crate::leanh::LeanObject,
    mut v_e_3506_: *mut crate::leanh::LeanObject,
    mut v_a_3507_: *mut crate::leanh::LeanObject,
    mut v_a_3508_: *mut crate::leanh::LeanObject,
    mut v_a_3509_: *mut crate::leanh::LeanObject,
    mut v_a_3510_: *mut crate::leanh::LeanObject,
    mut v_a_3511_: *mut crate::leanh::LeanObject,
    mut v_a_3512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3513_: u8 = 0;
    let mut v_res_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3513_ = (crate::leanh::lean_unbox(v_pu_3505_) as u8);
    v_res_3514_ = l_Lean_Compiler_LCNF_PP_ppLetValue(
        v_pu_boxed_3513_,
        v_e_3506_,
        v_a_3507_,
        v_a_3508_,
        v_a_3509_,
        v_a_3510_,
        v_a_3511_,
    );
    crate::leanh::lean_dec(v_a_3511_);
    crate::leanh::lean_dec_ref(v_a_3510_);
    crate::leanh::lean_dec(v_a_3509_);
    crate::leanh::lean_dec_ref(v_a_3508_);
    crate::leanh::lean_dec_ref(v_a_3507_);
    return v_res_3514_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParam___redArg(
    mut v_param_3519_: *mut crate::leanh::LeanObject,
    mut v_a_3520_: *mut crate::leanh::LeanObject,
    mut v_a_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_3526_: u8 = 0;
    let mut v___y_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: u8 = 0;
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_binderName_3524_ = crate::leanh::lean_ctor_get(v_param_3519_, 1);
                crate::leanh::lean_inc(v_binderName_3524_);
                v_type_3525_ = crate::leanh::lean_ctor_get(v_param_3519_, 2);
                crate::leanh::lean_inc_ref(v_type_3525_);
                v_borrow_3526_ = crate::leanh::lean_ctor_get_uint8(
                    v_param_3519_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_param_3519_);
                if v_borrow_3526_ == 0 {
                    v___x_3561_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20;
                    v___y_3528_ = v___x_3561_;
                    state = 1;
                    continue;
                } else {
                    v___x_3562_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2;
                    v___y_3528_ = v___x_3562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_options_3529_ = crate::leanh::lean_ctor_get(v_a_3521_, 2);
                v___x_3530_ = l_Lean_pp_funBinderTypes;
                v___x_3531_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                    v_options_3529_,
                    v___x_3530_,
                );
                if v___x_3531_ == 0 {
                    crate::leanh::lean_dec_ref(v_type_3525_);
                    v___x_3532_ = 1;
                    v___x_3533_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_binderName_3524_,
                        v___x_3532_,
                    );
                    crate::leanh::lean_inc_ref(v___y_3528_);
                    v___x_3534_ = lean_string_append(v___y_3528_, v___x_3533_);
                    crate::leanh::lean_dec_ref(v___x_3533_);
                    v___x_3535_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3535_, 0, v___x_3534_);
                    v___x_3536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3536_, 0, v___x_3535_);
                    return v___x_3536_;
                } else {
                    v___x_3537_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                        v_type_3525_,
                        v_a_3520_,
                        v_a_3521_,
                        v_a_3522_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3537_) == 0 {
                        v_a_3538_ = crate::leanh::lean_ctor_get(v___x_3537_, 0);
                        v_isSharedCheck_3560_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3537_)) as u8;
                        if v_isSharedCheck_3560_ == 0 {
                            v___x_3540_ = v___x_3537_;
                            v_isShared_3541_ = v_isSharedCheck_3560_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3538_);
                            crate::leanh::lean_dec(v___x_3537_);
                            v___x_3540_ = crate::leanh::lean_box(0);
                            v_isShared_3541_ = v_isSharedCheck_3560_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_binderName_3524_);
                        return v___x_3537_;
                    }
                }
            }
            2 => {
                v___x_3542_ = l_Lean_Name_toString(v_binderName_3524_, v___x_3531_);
                v___x_3543_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3543_, 0, v___x_3542_);
                v___x_3544_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_3545_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3545_, 0, v___x_3543_);
                crate::leanh::lean_ctor_set(v___x_3545_, 1, v___x_3544_);
                crate::leanh::lean_inc_ref(v___y_3528_);
                v___x_3546_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3546_, 0, v___y_3528_);
                v___x_3547_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3547_, 0, v___x_3545_);
                crate::leanh::lean_ctor_set(v___x_3547_, 1, v___x_3546_);
                v___x_3548_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3548_, 0, v___x_3547_);
                crate::leanh::lean_ctor_set(v___x_3548_, 1, v_a_3538_);
                v___x_3549_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once
                    ),
                    _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7,
                );
                v___x_3550_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8;
                v___x_3551_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3551_, 0, v___x_3550_);
                crate::leanh::lean_ctor_set(v___x_3551_, 1, v___x_3548_);
                v___x_3552_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9;
                v___x_3553_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3553_, 0, v___x_3551_);
                crate::leanh::lean_ctor_set(v___x_3553_, 1, v___x_3552_);
                v___x_3554_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3554_, 0, v___x_3549_);
                crate::leanh::lean_ctor_set(v___x_3554_, 1, v___x_3553_);
                v___x_3555_ = 0;
                v___x_3556_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3556_, 0, v___x_3554_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3556_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3555_,
                );
                if v_isShared_3541_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3540_, 0, v___x_3556_);
                    v___x_3558_ = v___x_3540_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
                    v___x_3558_ = v_reuseFailAlloc_3559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3558_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(
    mut v_param_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
    mut v_a_3566_: *mut crate::leanh::LeanObject,
    mut v_a_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3568_ =
        l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
    crate::leanh::lean_dec(v_a_3566_);
    crate::leanh::lean_dec_ref(v_a_3565_);
    crate::leanh::lean_dec_ref(v_a_3564_);
    return v_res_3568_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParam(
    mut v_pu_3569_: u8,
    mut v_param_3570_: *mut crate::leanh::LeanObject,
    mut v_a_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3577_ =
        l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_3570_, v_a_3571_, v_a_3574_, v_a_3575_);
    return v___x_3577_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParam___boxed(
    mut v_pu_3578_: *mut crate::leanh::LeanObject,
    mut v_param_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
    mut v_a_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
    mut v_a_3584_: *mut crate::leanh::LeanObject,
    mut v_a_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3586_: u8 = 0;
    let mut v_res_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3586_ = (crate::leanh::lean_unbox(v_pu_3578_) as u8);
    v_res_3587_ = l_Lean_Compiler_LCNF_PP_ppParam(
        v_pu_boxed_3586_,
        v_param_3579_,
        v_a_3580_,
        v_a_3581_,
        v_a_3582_,
        v_a_3583_,
        v_a_3584_,
    );
    crate::leanh::lean_dec(v_a_3584_);
    crate::leanh::lean_dec_ref(v_a_3583_);
    crate::leanh::lean_dec(v_a_3582_);
    crate::leanh::lean_dec_ref(v_a_3581_);
    crate::leanh::lean_dec_ref(v_a_3580_);
    return v_res_3587_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParams(
    mut v_pu_3588_: u8,
    mut v_params_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
    mut v_a_3591_: *mut crate::leanh::LeanObject,
    mut v_a_3592_: *mut crate::leanh::LeanObject,
    mut v_a_3593_: *mut crate::leanh::LeanObject,
    mut v_a_3594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3596_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
    v___x_3597_ = crate::leanh::lean_box((v_pu_3588_) as usize);
    v___x_3598_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PP_ppParam___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    crate::leanh::lean_closure_set(v___x_3598_, 0, v___x_3597_);
    v___x_3599_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(
            v___x_3596_,
            v_params_3589_,
            v___x_3598_,
            v_a_3590_,
            v_a_3591_,
            v_a_3592_,
            v_a_3593_,
            v_a_3594_,
        );
    return v___x_3599_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParams___boxed(
    mut v_pu_3600_: *mut crate::leanh::LeanObject,
    mut v_params_3601_: *mut crate::leanh::LeanObject,
    mut v_a_3602_: *mut crate::leanh::LeanObject,
    mut v_a_3603_: *mut crate::leanh::LeanObject,
    mut v_a_3604_: *mut crate::leanh::LeanObject,
    mut v_a_3605_: *mut crate::leanh::LeanObject,
    mut v_a_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3608_: u8 = 0;
    let mut v_res_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3608_ = (crate::leanh::lean_unbox(v_pu_3600_) as u8);
    v_res_3609_ = l_Lean_Compiler_LCNF_PP_ppParams(
        v_pu_boxed_3608_,
        v_params_3601_,
        v_a_3602_,
        v_a_3603_,
        v_a_3604_,
        v_a_3605_,
        v_a_3606_,
    );
    crate::leanh::lean_dec(v_a_3606_);
    crate::leanh::lean_dec_ref(v_a_3605_);
    crate::leanh::lean_dec(v_a_3604_);
    crate::leanh::lean_dec_ref(v_a_3603_);
    crate::leanh::lean_dec_ref(v_a_3602_);
    crate::leanh::lean_dec_ref(v_params_3601_);
    return v_res_3609_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLetDecl(
    mut v_pu_3616_: u8,
    mut v_letDecl_3617_: *mut crate::leanh::LeanObject,
    mut v_a_3618_: *mut crate::leanh::LeanObject,
    mut v_a_3619_: *mut crate::leanh::LeanObject,
    mut v_a_3620_: *mut crate::leanh::LeanObject,
    mut v_a_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: u8 = 0;
    let mut v_binderName_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3633_: u8 = 0;
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: u8 = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut v_binderName_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3624_ = crate::leanh::lean_ctor_get(v_a_3621_, 2);
                v___x_3625_ = l_Lean_pp_letVarTypes;
                v___x_3626_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                    v_options_3624_,
                    v___x_3625_,
                );
                if v___x_3626_ == 0 {
                    v_binderName_3627_ = crate::leanh::lean_ctor_get(v_letDecl_3617_, 1);
                    crate::leanh::lean_inc(v_binderName_3627_);
                    v_value_3628_ = crate::leanh::lean_ctor_get(v_letDecl_3617_, 3);
                    crate::leanh::lean_inc(v_value_3628_);
                    crate::leanh::lean_dec_ref(v_letDecl_3617_);
                    v___x_3629_ = l_Lean_Compiler_LCNF_PP_ppLetValue(
                        v_pu_3616_,
                        v_value_3628_,
                        v_a_3618_,
                        v_a_3619_,
                        v_a_3620_,
                        v_a_3621_,
                        v_a_3622_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3629_) == 0 {
                        v_a_3630_ = crate::leanh::lean_ctor_get(v___x_3629_, 0);
                        v_isSharedCheck_3645_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3629_)) as u8;
                        if v_isSharedCheck_3645_ == 0 {
                            v___x_3632_ = v___x_3629_;
                            v_isShared_3633_ = v_isSharedCheck_3645_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3630_);
                            crate::leanh::lean_dec(v___x_3629_);
                            v___x_3632_ = crate::leanh::lean_box(0);
                            v_isShared_3633_ = v_isSharedCheck_3645_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_binderName_3627_);
                        return v___x_3629_;
                    }
                } else {
                    v_binderName_3646_ = crate::leanh::lean_ctor_get(v_letDecl_3617_, 1);
                    crate::leanh::lean_inc(v_binderName_3646_);
                    v_type_3647_ = crate::leanh::lean_ctor_get(v_letDecl_3617_, 2);
                    crate::leanh::lean_inc_ref(v_type_3647_);
                    v_value_3648_ = crate::leanh::lean_ctor_get(v_letDecl_3617_, 3);
                    crate::leanh::lean_inc(v_value_3648_);
                    crate::leanh::lean_dec_ref(v_letDecl_3617_);
                    v___x_3649_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                        v_type_3647_,
                        v_a_3618_,
                        v_a_3621_,
                        v_a_3622_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3649_) == 0 {
                        v_a_3650_ = crate::leanh::lean_ctor_get(v___x_3649_, 0);
                        v_isSharedCheck_3675_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3649_)) as u8;
                        if v_isSharedCheck_3675_ == 0 {
                            v___x_3652_ = v___x_3649_;
                            v_isShared_3653_ = v_isSharedCheck_3675_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3650_);
                            crate::leanh::lean_dec(v___x_3649_);
                            v___x_3652_ = crate::leanh::lean_box(0);
                            v_isShared_3653_ = v_isSharedCheck_3675_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_value_3648_);
                        crate::leanh::lean_dec(v_binderName_3646_);
                        return v___x_3649_;
                    }
                }
            }
            1 => {
                v___x_3634_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1;
                v___x_3635_ = 1;
                v___x_3636_ = l_Lean_Name_toString(v_binderName_3627_, v___x_3635_);
                v___x_3637_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3637_, 0, v___x_3636_);
                v___x_3638_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3638_, 0, v___x_3634_);
                crate::leanh::lean_ctor_set(v___x_3638_, 1, v___x_3637_);
                v___x_3639_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
                v___x_3640_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3640_, 0, v___x_3638_);
                crate::leanh::lean_ctor_set(v___x_3640_, 1, v___x_3639_);
                v___x_3641_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3641_, 0, v___x_3640_);
                crate::leanh::lean_ctor_set(v___x_3641_, 1, v_a_3630_);
                if v_isShared_3633_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3632_, 0, v___x_3641_);
                    v___x_3643_ = v___x_3632_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
                    v___x_3643_ = v_reuseFailAlloc_3644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3643_;
            }
            3 => {
                v___x_3654_ = l_Lean_Compiler_LCNF_PP_ppLetValue(
                    v_pu_3616_,
                    v_value_3648_,
                    v_a_3618_,
                    v_a_3619_,
                    v_a_3620_,
                    v_a_3621_,
                    v_a_3622_,
                );
                if crate::leanh::lean_obj_tag(v___x_3654_) == 0 {
                    v_a_3655_ = crate::leanh::lean_ctor_get(v___x_3654_, 0);
                    v_isSharedCheck_3674_ = (!crate::leanh::lean_is_exclusive(v___x_3654_)) as u8;
                    if v_isSharedCheck_3674_ == 0 {
                        v___x_3657_ = v___x_3654_;
                        v_isShared_3658_ = v_isSharedCheck_3674_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3655_);
                        crate::leanh::lean_dec(v___x_3654_);
                        v___x_3657_ = crate::leanh::lean_box(0);
                        v_isShared_3658_ = v_isSharedCheck_3674_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3652_);
                    crate::leanh::lean_dec(v_a_3650_);
                    crate::leanh::lean_dec(v_binderName_3646_);
                    return v___x_3654_;
                }
            }
            4 => {
                v___x_3659_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1;
                v___x_3660_ = l_Lean_Name_toString(v_binderName_3646_, v___x_3626_);
                if v_isShared_3653_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3652_, 3);
                    crate::leanh::lean_ctor_set(v___x_3652_, 0, v___x_3660_);
                    v___x_3662_ = v___x_3652_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3660_);
                    v___x_3662_ = v_reuseFailAlloc_3673_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3663_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3663_, 0, v___x_3659_);
                crate::leanh::lean_ctor_set(v___x_3663_, 1, v___x_3662_);
                v___x_3664_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_3665_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3665_, 0, v___x_3663_);
                crate::leanh::lean_ctor_set(v___x_3665_, 1, v___x_3664_);
                v___x_3666_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3666_, 0, v___x_3665_);
                crate::leanh::lean_ctor_set(v___x_3666_, 1, v_a_3650_);
                v___x_3667_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
                v___x_3668_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3668_, 0, v___x_3666_);
                crate::leanh::lean_ctor_set(v___x_3668_, 1, v___x_3667_);
                v___x_3669_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3669_, 0, v___x_3668_);
                crate::leanh::lean_ctor_set(v___x_3669_, 1, v_a_3655_);
                if v_isShared_3658_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3657_, 0, v___x_3669_);
                    v___x_3671_ = v___x_3657_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
                    v___x_3671_ = v_reuseFailAlloc_3672_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3671_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(
    mut v_pu_3676_: *mut crate::leanh::LeanObject,
    mut v_letDecl_3677_: *mut crate::leanh::LeanObject,
    mut v_a_3678_: *mut crate::leanh::LeanObject,
    mut v_a_3679_: *mut crate::leanh::LeanObject,
    mut v_a_3680_: *mut crate::leanh::LeanObject,
    mut v_a_3681_: *mut crate::leanh::LeanObject,
    mut v_a_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3684_: u8 = 0;
    let mut v_res_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3684_ = (crate::leanh::lean_unbox(v_pu_3676_) as u8);
    v_res_3685_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(
        v_pu_boxed_3684_,
        v_letDecl_3677_,
        v_a_3678_,
        v_a_3679_,
        v_a_3680_,
        v_a_3681_,
        v_a_3682_,
    );
    crate::leanh::lean_dec(v_a_3682_);
    crate::leanh::lean_dec_ref(v_a_3681_);
    crate::leanh::lean_dec(v_a_3680_);
    crate::leanh::lean_dec_ref(v_a_3679_);
    crate::leanh::lean_dec_ref(v_a_3678_);
    return v_res_3685_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(
    mut v_sz_3686_: usize,
    mut v_i_3687_: usize,
    mut v_bs_3688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3689_: u8 = 0;
    let mut v_v_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: usize = 0;
    let mut v___x_3696_: usize = 0;
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3689_ = lean_usize_dec_lt(v_i_3687_, v_sz_3686_);
                if v___x_3689_ == 0 {
                    return v_bs_3688_;
                } else {
                    v_v_3690_ = lean_array_uget_borrowed(v_bs_3688_, v_i_3687_);
                    v_fvarId_3691_ = crate::leanh::lean_ctor_get(v_v_3690_, 0);
                    crate::leanh::lean_inc(v_fvarId_3691_);
                    v___x_3692_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3693_ = lean_array_uset(v_bs_3688_, v_i_3687_, v___x_3692_);
                    v___x_3694_ = l_Lean_mkFVar(v_fvarId_3691_);
                    v___x_3695_ = 1usize;
                    v___x_3696_ = lean_usize_add(v_i_3687_, v___x_3695_);
                    v___x_3697_ = lean_array_uset(v_bs_x27_3693_, v_i_3687_, v___x_3694_);
                    v_i_3687_ = v___x_3696_;
                    v_bs_3688_ = v___x_3697_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(
    mut v_sz_3699_: *mut crate::leanh::LeanObject,
    mut v_i_3700_: *mut crate::leanh::LeanObject,
    mut v_bs_3701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3702_: usize = 0;
    let mut v_i_boxed_3703_: usize = 0;
    let mut v_res_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3702_ = crate::leanh::lean_unbox_usize(v_sz_3699_);
    crate::leanh::lean_dec(v_sz_3699_);
    v_i_boxed_3703_ = crate::leanh::lean_unbox_usize(v_i_3700_);
    crate::leanh::lean_dec(v_i_3700_);
    v_res_3704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_boxed_3702_, v_i_boxed_3703_, v_bs_3701_);
    return v_res_3704_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_getFunType(
    mut v_pu_3705_: u8,
    mut v_ps_3706_: *mut crate::leanh::LeanObject,
    mut v_type_3707_: *mut crate::leanh::LeanObject,
    mut v_a_3708_: *mut crate::leanh::LeanObject,
    mut v_a_3709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3711_: u8 = 0;
    v___x_3711_ = l_Lean_Expr_isErased(v_type_3707_);
    if v___x_3711_ == 0 {
        if v_pu_3705_ == 0 {
            let mut v_sz_3712_: usize = 0;
            let mut v___x_3713_: usize = 0;
            let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_sz_3712_ = lean_array_size(v_ps_3706_);
            v___x_3713_ = 0usize;
            v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_3712_, v___x_3713_, v_ps_3706_);
            v___x_3715_ = l_Lean_Compiler_LCNF_instantiateForall(
                v_type_3707_,
                v___x_3714_,
                v_a_3708_,
                v_a_3709_,
            );
            crate::leanh::lean_dec_ref(v___x_3714_);
            return v___x_3715_;
        } else {
            let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_ps_3706_);
            v___x_3716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3716_, 0, v_type_3707_);
            return v___x_3716_;
        }
    } else {
        let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_ps_3706_);
        v___x_3717_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3717_, 0, v_type_3707_);
        return v___x_3717_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_getFunType___boxed(
    mut v_pu_3718_: *mut crate::leanh::LeanObject,
    mut v_ps_3719_: *mut crate::leanh::LeanObject,
    mut v_type_3720_: *mut crate::leanh::LeanObject,
    mut v_a_3721_: *mut crate::leanh::LeanObject,
    mut v_a_3722_: *mut crate::leanh::LeanObject,
    mut v_a_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3724_: u8 = 0;
    let mut v_res_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3724_ = (crate::leanh::lean_unbox(v_pu_3718_) as u8);
    v_res_3725_ = l_Lean_Compiler_LCNF_PP_getFunType(
        v_pu_boxed_3724_,
        v_ps_3719_,
        v_type_3720_,
        v_a_3721_,
        v_a_3722_,
    );
    crate::leanh::lean_dec(v_a_3722_);
    crate::leanh::lean_dec_ref(v_a_3721_);
    return v_res_3725_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppAlt(
    mut v_pu_3750_: u8,
    mut v_alt_3751_: *mut crate::leanh::LeanObject,
    mut v_a_3752_: *mut crate::leanh::LeanObject,
    mut v_a_3753_: *mut crate::leanh::LeanObject,
    mut v_a_3754_: *mut crate::leanh::LeanObject,
    mut v_a_3755_: *mut crate::leanh::LeanObject,
    mut v_a_3756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctorName_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3770_: u8 = 0;
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: u8 = 0;
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3786_: u8 = 0;
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_info_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3792_: u8 = 0;
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v_name_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3813_: u8 = 0;
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v_code_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3820_: u8 = 0;
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_alt_3751_) {
                0 => {
                    v_ctorName_3758_ = crate::leanh::lean_ctor_get(v_alt_3751_, 0);
                    crate::leanh::lean_inc(v_ctorName_3758_);
                    v_params_3759_ = crate::leanh::lean_ctor_get(v_alt_3751_, 1);
                    crate::leanh::lean_inc_ref(v_params_3759_);
                    v_code_3760_ = crate::leanh::lean_ctor_get(v_alt_3751_, 2);
                    crate::leanh::lean_inc_ref(v_code_3760_);
                    crate::leanh::lean_dec_ref_known(v_alt_3751_, 3);
                    v___x_3761_ = l_Lean_Compiler_LCNF_PP_ppParams(
                        v_pu_3750_,
                        v_params_3759_,
                        v_a_3752_,
                        v_a_3753_,
                        v_a_3754_,
                        v_a_3755_,
                        v_a_3756_,
                    );
                    crate::leanh::lean_dec_ref(v_params_3759_);
                    if crate::leanh::lean_obj_tag(v___x_3761_) == 0 {
                        v_a_3762_ = crate::leanh::lean_ctor_get(v___x_3761_, 0);
                        v_isSharedCheck_3787_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3761_)) as u8;
                        if v_isSharedCheck_3787_ == 0 {
                            v___x_3764_ = v___x_3761_;
                            v_isShared_3765_ = v_isSharedCheck_3787_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3762_);
                            crate::leanh::lean_dec(v___x_3761_);
                            v___x_3764_ = crate::leanh::lean_box(0);
                            v_isShared_3765_ = v_isSharedCheck_3787_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_code_3760_);
                        crate::leanh::lean_dec(v_ctorName_3758_);
                        return v___x_3761_;
                    }
                }
                1 => {
                    v_info_3788_ = crate::leanh::lean_ctor_get(v_alt_3751_, 0);
                    v_code_3789_ = crate::leanh::lean_ctor_get(v_alt_3751_, 1);
                    v_isSharedCheck_3814_ = (!crate::leanh::lean_is_exclusive(v_alt_3751_)) as u8;
                    if v_isSharedCheck_3814_ == 0 {
                        v___x_3791_ = v_alt_3751_;
                        v_isShared_3792_ = v_isSharedCheck_3814_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_3789_);
                        crate::leanh::lean_inc(v_info_3788_);
                        crate::leanh::lean_dec(v_alt_3751_);
                        v___x_3791_ = crate::leanh::lean_box(0);
                        v_isShared_3792_ = v_isSharedCheck_3814_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_code_3815_ = crate::leanh::lean_ctor_get(v_alt_3751_, 0);
                    crate::leanh::lean_inc_ref(v_code_3815_);
                    crate::leanh::lean_dec_ref_known(v_alt_3751_, 1);
                    v___x_3816_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3750_,
                        v_code_3815_,
                        v_a_3752_,
                        v_a_3753_,
                        v_a_3754_,
                        v_a_3755_,
                        v_a_3756_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3816_) == 0 {
                        v_a_3817_ = crate::leanh::lean_ctor_get(v___x_3816_, 0);
                        v_isSharedCheck_3827_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3816_)) as u8;
                        if v_isSharedCheck_3827_ == 0 {
                            v___x_3819_ = v___x_3816_;
                            v_isShared_3820_ = v_isSharedCheck_3827_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3817_);
                            crate::leanh::lean_dec(v___x_3816_);
                            v___x_3819_ = crate::leanh::lean_box(0);
                            v_isShared_3820_ = v_isSharedCheck_3827_;
                            state = 9;
                            continue;
                        }
                    } else {
                        return v___x_3816_;
                    }
                }
            },
            1 => {
                v___x_3766_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3750_,
                    v_code_3760_,
                    v_a_3752_,
                    v_a_3753_,
                    v_a_3754_,
                    v_a_3755_,
                    v_a_3756_,
                );
                if crate::leanh::lean_obj_tag(v___x_3766_) == 0 {
                    v_a_3767_ = crate::leanh::lean_ctor_get(v___x_3766_, 0);
                    v_isSharedCheck_3786_ = (!crate::leanh::lean_is_exclusive(v___x_3766_)) as u8;
                    if v_isSharedCheck_3786_ == 0 {
                        v___x_3769_ = v___x_3766_;
                        v_isShared_3770_ = v_isSharedCheck_3786_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3767_);
                        crate::leanh::lean_dec(v___x_3766_);
                        v___x_3769_ = crate::leanh::lean_box(0);
                        v_isShared_3770_ = v_isSharedCheck_3786_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3764_);
                    crate::leanh::lean_dec(v_a_3762_);
                    crate::leanh::lean_dec(v_ctorName_3758_);
                    return v___x_3766_;
                }
            }
            2 => {
                v___x_3771_ = l_Lean_Compiler_LCNF_PP_ppAlt___closed__1;
                v___x_3772_ = 1;
                v___x_3773_ = l_Lean_Name_toString(v_ctorName_3758_, v___x_3772_);
                if v_isShared_3765_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3764_, 3);
                    crate::leanh::lean_ctor_set(v___x_3764_, 0, v___x_3773_);
                    v___x_3775_ = v___x_3764_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3785_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3773_);
                    v___x_3775_ = v_reuseFailAlloc_3785_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3776_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3776_, 0, v___x_3771_);
                crate::leanh::lean_ctor_set(v___x_3776_, 1, v___x_3775_);
                v___x_3777_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3777_, 0, v___x_3776_);
                crate::leanh::lean_ctor_set(v___x_3777_, 1, v_a_3762_);
                v___x_3778_ = l_Lean_Compiler_LCNF_PP_ppAlt___closed__3;
                v___x_3779_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3779_, 0, v___x_3777_);
                crate::leanh::lean_ctor_set(v___x_3779_, 1, v___x_3778_);
                v___x_3780_ = l_Std_Format_indentD(v_a_3767_);
                v___x_3781_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3781_, 0, v___x_3779_);
                crate::leanh::lean_ctor_set(v___x_3781_, 1, v___x_3780_);
                if v_isShared_3770_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3769_, 0, v___x_3781_);
                    v___x_3783_ = v___x_3769_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3784_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
                    v___x_3783_ = v_reuseFailAlloc_3784_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3783_;
            }
            5 => {
                v___x_3793_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3750_,
                    v_code_3789_,
                    v_a_3752_,
                    v_a_3753_,
                    v_a_3754_,
                    v_a_3755_,
                    v_a_3756_,
                );
                if crate::leanh::lean_obj_tag(v___x_3793_) == 0 {
                    v_a_3794_ = crate::leanh::lean_ctor_get(v___x_3793_, 0);
                    v_isSharedCheck_3813_ = (!crate::leanh::lean_is_exclusive(v___x_3793_)) as u8;
                    if v_isSharedCheck_3813_ == 0 {
                        v___x_3796_ = v___x_3793_;
                        v_isShared_3797_ = v_isSharedCheck_3813_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3794_);
                        crate::leanh::lean_dec(v___x_3793_);
                        v___x_3796_ = crate::leanh::lean_box(0);
                        v_isShared_3797_ = v_isSharedCheck_3813_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3791_);
                    crate::leanh::lean_dec_ref(v_info_3788_);
                    return v___x_3793_;
                }
            }
            6 => {
                v_name_3798_ = crate::leanh::lean_ctor_get(v_info_3788_, 0);
                crate::leanh::lean_inc(v_name_3798_);
                crate::leanh::lean_dec_ref(v_info_3788_);
                v___x_3799_ = l_Lean_Compiler_LCNF_PP_ppAlt___closed__1;
                v___x_3800_ = 1;
                v___x_3801_ = l_Lean_Name_toString(v_name_3798_, v___x_3800_);
                v___x_3802_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3802_, 0, v___x_3801_);
                if v_isShared_3792_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3791_, 5);
                    crate::leanh::lean_ctor_set(v___x_3791_, 1, v___x_3802_);
                    crate::leanh::lean_ctor_set(v___x_3791_, 0, v___x_3799_);
                    v___x_3804_ = v___x_3791_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3812_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 1, v___x_3802_);
                    v___x_3804_ = v_reuseFailAlloc_3812_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3805_ = l_Lean_Compiler_LCNF_PP_ppAlt___closed__3;
                v___x_3806_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3806_, 0, v___x_3804_);
                crate::leanh::lean_ctor_set(v___x_3806_, 1, v___x_3805_);
                v___x_3807_ = l_Std_Format_indentD(v_a_3794_);
                v___x_3808_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3808_, 0, v___x_3806_);
                crate::leanh::lean_ctor_set(v___x_3808_, 1, v___x_3807_);
                if v_isShared_3797_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3796_, 0, v___x_3808_);
                    v___x_3810_ = v___x_3796_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3811_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
                    v___x_3810_ = v_reuseFailAlloc_3811_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3810_;
            }
            9 => {
                v___x_3821_ = l_Lean_Compiler_LCNF_PP_ppAlt___closed__5;
                v___x_3822_ = l_Std_Format_indentD(v_a_3817_);
                v___x_3823_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3823_, 0, v___x_3821_);
                crate::leanh::lean_ctor_set(v___x_3823_, 1, v___x_3822_);
                if v_isShared_3820_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3819_, 0, v___x_3823_);
                    v___x_3825_ = v___x_3819_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
                    v___x_3825_ = v_reuseFailAlloc_3826_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppAlt___boxed(
    mut v_pu_3828_: *mut crate::leanh::LeanObject,
    mut v_alt_3829_: *mut crate::leanh::LeanObject,
    mut v_a_3830_: *mut crate::leanh::LeanObject,
    mut v_a_3831_: *mut crate::leanh::LeanObject,
    mut v_a_3832_: *mut crate::leanh::LeanObject,
    mut v_a_3833_: *mut crate::leanh::LeanObject,
    mut v_a_3834_: *mut crate::leanh::LeanObject,
    mut v_a_3835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3836_: u8 = 0;
    let mut v_res_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3836_ = (crate::leanh::lean_unbox(v_pu_3828_) as u8);
    v_res_3837_ = l_Lean_Compiler_LCNF_PP_ppAlt(
        v_pu_boxed_3836_,
        v_alt_3829_,
        v_a_3830_,
        v_a_3831_,
        v_a_3832_,
        v_a_3833_,
        v_a_3834_,
    );
    crate::leanh::lean_dec(v_a_3834_);
    crate::leanh::lean_dec_ref(v_a_3833_);
    crate::leanh::lean_dec(v_a_3832_);
    crate::leanh::lean_dec_ref(v_a_3831_);
    crate::leanh::lean_dec_ref(v_a_3830_);
    return v_res_3837_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppCode(
    mut v_pu_3889_: u8,
    mut v_c_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3908_: u8 = 0;
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut v_isSharedCheck_3920_: u8 = 0;
    let mut v_decl_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3932_: u8 = 0;
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3945_: u8 = 0;
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v_decl_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3971_: u8 = 0;
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v_fvarId_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3977_: u8 = 0;
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3984_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3993_: u8 = 0;
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v_cases_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4010_: u8 = 0;
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v_fvarId_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4032_: u8 = 0;
    let mut v_type_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4036_: u8 = 0;
    let mut v_options_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4048_: u8 = 0;
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4054_: u8 = 0;
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut v_fvarId_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4066_: u8 = 0;
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4071_: u8 = 0;
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut v_fvarId_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4130_: u8 = 0;
    let mut v_isSharedCheck_4131_: u8 = 0;
    let mut v_fvarId_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: u8 = 0;
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4150_: u8 = 0;
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4155_: u8 = 0;
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_isSharedCheck_4184_: u8 = 0;
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4197_: u8 = 0;
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4202_: u8 = 0;
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_isSharedCheck_4234_: u8 = 0;
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut v_fvarId_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4243_: u8 = 0;
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut v_isSharedCheck_4267_: u8 = 0;
    let mut v_fvarId_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_4270_: u8 = 0;
    let mut v_persistent_4271_: u8 = 0;
    let mut v_k_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: u8 = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4283_: u8 = 0;
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v_isSharedCheck_4311_: u8 = 0;
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_isSharedCheck_4339_: u8 = 0;
    let mut v___y_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_4348_: u8 = 0;
    let mut v_persistent_4349_: u8 = 0;
    let mut v_objs_x3f_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4365_: u8 = 0;
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4370_: u8 = 0;
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut v_isSharedCheck_4393_: u8 = 0;
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4420_: u8 = 0;
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut v_ann_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4471_: u8 = 0;
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_c_3890_) {
                0 => {
                    v_decl_3897_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    v_k_3898_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_3920_ = (!crate::leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_3920_ == 0 {
                        v___x_3900_ = v_c_3890_;
                        v_isShared_3901_ = v_isSharedCheck_3920_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_3898_);
                        crate::leanh::lean_inc(v_decl_3897_);
                        crate::leanh::lean_dec(v_c_3890_);
                        v___x_3900_ = crate::leanh::lean_box(0);
                        v_isShared_3901_ = v_isSharedCheck_3920_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_decl_3921_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    v_k_3922_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_3946_ = (!crate::leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_3946_ == 0 {
                        v___x_3924_ = v_c_3890_;
                        v_isShared_3925_ = v_isSharedCheck_3946_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_3922_);
                        crate::leanh::lean_inc(v_decl_3921_);
                        crate::leanh::lean_dec(v_c_3890_);
                        v___x_3924_ = crate::leanh::lean_box(0);
                        v_isShared_3925_ = v_isSharedCheck_3946_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_decl_3947_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    v_k_3948_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_3972_ = (!crate::leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_3972_ == 0 {
                        v___x_3950_ = v_c_3890_;
                        v_isShared_3951_ = v_isSharedCheck_3972_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_3948_);
                        crate::leanh::lean_inc(v_decl_3947_);
                        crate::leanh::lean_dec(v_c_3890_);
                        v___x_3950_ = crate::leanh::lean_box(0);
                        v_isShared_3951_ = v_isSharedCheck_3972_;
                        state = 9;
                        continue;
                    }
                }
                3 => {
                    v_fvarId_3973_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    v_args_3974_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_3994_ = (!crate::leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_3994_ == 0 {
                        v___x_3976_ = v_c_3890_;
                        v_isShared_3977_ = v_isSharedCheck_3994_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_args_3974_);
                        crate::leanh::lean_inc(v_fvarId_3973_);
                        crate::leanh::lean_dec(v_c_3890_);
                        v___x_3976_ = crate::leanh::lean_box(0);
                        v_isShared_3977_ = v_isSharedCheck_3994_;
                        state = 13;
                        continue;
                    }
                }
                4 => {
                    v_cases_3995_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    crate::leanh::lean_inc_ref(v_cases_3995_);
                    crate::leanh::lean_dec_ref_known(v_c_3890_, 1);
                    v_resultType_3996_ = crate::leanh::lean_ctor_get(v_cases_3995_, 1);
                    crate::leanh::lean_inc_ref(v_resultType_3996_);
                    v_discr_3997_ = crate::leanh::lean_ctor_get(v_cases_3995_, 2);
                    crate::leanh::lean_inc(v_discr_3997_);
                    v_alts_3998_ = crate::leanh::lean_ctor_get(v_cases_3995_, 3);
                    crate::leanh::lean_inc_ref(v_alts_3998_);
                    crate::leanh::lean_dec_ref(v_cases_3995_);
                    v___x_3999_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_discr_3997_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3999_) == 0 {
                        v_a_4000_ = crate::leanh::lean_ctor_get(v___x_3999_, 0);
                        crate::leanh::lean_inc(v_a_4000_);
                        crate::leanh::lean_dec_ref_known(v___x_3999_, 1);
                        v___x_4001_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                            v_resultType_3996_,
                            v_a_3891_,
                            v_a_3894_,
                            v_a_3895_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4001_) == 0 {
                            v_a_4002_ = crate::leanh::lean_ctor_get(v___x_4001_, 0);
                            crate::leanh::lean_inc(v_a_4002_);
                            crate::leanh::lean_dec_ref_known(v___x_4001_, 1);
                            v___x_4003_ = crate::leanh::lean_box(1);
                            v___x_4004_ = crate::leanh::lean_box((v_pu_3889_) as usize);
                            v___x_4005_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Compiler_LCNF_PP_ppAlt___boxed as *mut core::ffi::c_void,
                                8,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___x_4005_, 0, v___x_4004_);
                            v___x_4006_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_4003_, v_alts_3998_, v___x_4005_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
                            crate::leanh::lean_dec_ref(v_alts_3998_);
                            if crate::leanh::lean_obj_tag(v___x_4006_) == 0 {
                                v_a_4007_ = crate::leanh::lean_ctor_get(v___x_4006_, 0);
                                v_isSharedCheck_4020_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4006_)) as u8;
                                if v_isSharedCheck_4020_ == 0 {
                                    v___x_4009_ = v___x_4006_;
                                    v_isShared_4010_ = v_isSharedCheck_4020_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4007_);
                                    crate::leanh::lean_dec(v___x_4006_);
                                    v___x_4009_ = crate::leanh::lean_box(0);
                                    v_isShared_4010_ = v_isSharedCheck_4020_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4002_);
                                crate::leanh::lean_dec(v_a_4000_);
                                return v___x_4006_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4000_);
                            crate::leanh::lean_dec_ref(v_alts_3998_);
                            return v___x_4001_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_alts_3998_);
                        crate::leanh::lean_dec_ref(v_resultType_3996_);
                        return v___x_3999_;
                    }
                }
                5 => {
                    v_fvarId_4021_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    crate::leanh::lean_inc(v_fvarId_4021_);
                    crate::leanh::lean_dec_ref_known(v_c_3890_, 1);
                    v___x_4022_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4021_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4022_) == 0 {
                        v_a_4023_ = crate::leanh::lean_ctor_get(v___x_4022_, 0);
                        v_isSharedCheck_4032_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4022_)) as u8;
                        if v_isSharedCheck_4032_ == 0 {
                            v___x_4025_ = v___x_4022_;
                            v_isShared_4026_ = v_isSharedCheck_4032_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4023_);
                            crate::leanh::lean_dec(v___x_4022_);
                            v___x_4025_ = crate::leanh::lean_box(0);
                            v_isShared_4026_ = v_isSharedCheck_4032_;
                            state = 19;
                            continue;
                        }
                    } else {
                        return v___x_4022_;
                    }
                }
                6 => {
                    v_type_4033_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    v_isSharedCheck_4055_ = (!crate::leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_4055_ == 0 {
                        v___x_4035_ = v_c_3890_;
                        v_isShared_4036_ = v_isSharedCheck_4055_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_type_4033_);
                        crate::leanh::lean_dec(v_c_3890_);
                        v___x_4035_ = crate::leanh::lean_box(0);
                        v_isShared_4036_ = v_isSharedCheck_4055_;
                        state = 21;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_4056_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    crate::leanh::lean_inc(v_fvarId_4056_);
                    v_i_4057_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    crate::leanh::lean_inc(v_i_4057_);
                    v_y_4058_ = crate::leanh::lean_ctor_get(v_c_3890_, 2);
                    crate::leanh::lean_inc(v_y_4058_);
                    v_k_4059_ = crate::leanh::lean_ctor_get(v_c_3890_, 3);
                    crate::leanh::lean_inc_ref(v_k_4059_);
                    crate::leanh::lean_dec_ref_known(v_c_3890_, 4);
                    v___x_4060_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4056_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4060_) == 0 {
                        v_a_4061_ = crate::leanh::lean_ctor_get(v___x_4060_, 0);
                        crate::leanh::lean_inc(v_a_4061_);
                        crate::leanh::lean_dec_ref_known(v___x_4060_, 1);
                        v___x_4062_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(
                            v_y_4058_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4062_) == 0 {
                            v_a_4063_ = crate::leanh::lean_ctor_get(v___x_4062_, 0);
                            v_isSharedCheck_4093_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4062_)) as u8;
                            if v_isSharedCheck_4093_ == 0 {
                                v___x_4065_ = v___x_4062_;
                                v_isShared_4066_ = v_isSharedCheck_4093_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4063_);
                                crate::leanh::lean_dec(v___x_4062_);
                                v___x_4065_ = crate::leanh::lean_box(0);
                                v_isShared_4066_ = v_isSharedCheck_4093_;
                                state = 25;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4061_);
                            crate::leanh::lean_dec_ref(v_k_4059_);
                            crate::leanh::lean_dec(v_i_4057_);
                            return v___x_4062_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_4059_);
                        crate::leanh::lean_dec(v_y_4058_);
                        crate::leanh::lean_dec(v_i_4057_);
                        return v___x_4060_;
                    }
                }
                8 => {
                    v_fvarId_4094_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    crate::leanh::lean_inc(v_fvarId_4094_);
                    v_i_4095_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    crate::leanh::lean_inc(v_i_4095_);
                    v_y_4096_ = crate::leanh::lean_ctor_get(v_c_3890_, 2);
                    crate::leanh::lean_inc(v_y_4096_);
                    v_k_4097_ = crate::leanh::lean_ctor_get(v_c_3890_, 3);
                    crate::leanh::lean_inc_ref(v_k_4097_);
                    crate::leanh::lean_dec_ref_known(v_c_3890_, 4);
                    v___x_4098_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4094_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4098_) == 0 {
                        v_a_4099_ = crate::leanh::lean_ctor_get(v___x_4098_, 0);
                        crate::leanh::lean_inc(v_a_4099_);
                        crate::leanh::lean_dec_ref_known(v___x_4098_, 1);
                        v___x_4100_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                            v_y_4096_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4100_) == 0 {
                            v_a_4101_ = crate::leanh::lean_ctor_get(v___x_4100_, 0);
                            v_isSharedCheck_4131_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4100_)) as u8;
                            if v_isSharedCheck_4131_ == 0 {
                                v___x_4103_ = v___x_4100_;
                                v_isShared_4104_ = v_isSharedCheck_4131_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4101_);
                                crate::leanh::lean_dec(v___x_4100_);
                                v___x_4103_ = crate::leanh::lean_box(0);
                                v_isShared_4104_ = v_isSharedCheck_4131_;
                                state = 29;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4099_);
                            crate::leanh::lean_dec_ref(v_k_4097_);
                            crate::leanh::lean_dec(v_i_4095_);
                            return v___x_4100_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_4097_);
                        crate::leanh::lean_dec(v_y_4096_);
                        crate::leanh::lean_dec(v_i_4095_);
                        return v___x_4098_;
                    }
                }
                9 => {
                    v_fvarId_4132_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    crate::leanh::lean_inc(v_fvarId_4132_);
                    v_i_4133_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    crate::leanh::lean_inc(v_i_4133_);
                    v_offset_4134_ = crate::leanh::lean_ctor_get(v_c_3890_, 2);
                    crate::leanh::lean_inc(v_offset_4134_);
                    v_y_4135_ = crate::leanh::lean_ctor_get(v_c_3890_, 3);
                    crate::leanh::lean_inc(v_y_4135_);
                    v_ty_4136_ = crate::leanh::lean_ctor_get(v_c_3890_, 4);
                    crate::leanh::lean_inc_ref(v_ty_4136_);
                    v_k_4137_ = crate::leanh::lean_ctor_get(v_c_3890_, 5);
                    crate::leanh::lean_inc_ref(v_k_4137_);
                    crate::leanh::lean_dec_ref_known(v_c_3890_, 6);
                    v_options_4138_ = crate::leanh::lean_ctor_get(v_a_3894_, 2);
                    v___x_4139_ = l_Lean_pp_letVarTypes;
                    v___x_4140_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                        v_options_4138_,
                        v___x_4139_,
                    );
                    if v___x_4140_ == 0 {
                        crate::leanh::lean_dec_ref(v_ty_4136_);
                        v___x_4141_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                            v_fvarId_4132_,
                            v_a_3892_,
                            v_a_3893_,
                            v_a_3894_,
                            v_a_3895_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4141_) == 0 {
                            v_a_4142_ = crate::leanh::lean_ctor_get(v___x_4141_, 0);
                            v_isSharedCheck_4185_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4141_)) as u8;
                            if v_isSharedCheck_4185_ == 0 {
                                v___x_4144_ = v___x_4141_;
                                v_isShared_4145_ = v_isSharedCheck_4185_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4142_);
                                crate::leanh::lean_dec(v___x_4141_);
                                v___x_4144_ = crate::leanh::lean_box(0);
                                v_isShared_4145_ = v_isSharedCheck_4185_;
                                state = 33;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_4137_);
                            crate::leanh::lean_dec(v_y_4135_);
                            crate::leanh::lean_dec(v_offset_4134_);
                            crate::leanh::lean_dec(v_i_4133_);
                            return v___x_4141_;
                        }
                    } else {
                        v___x_4186_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                            v_fvarId_4132_,
                            v_a_3892_,
                            v_a_3893_,
                            v_a_3894_,
                            v_a_3895_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4186_) == 0 {
                            v_a_4187_ = crate::leanh::lean_ctor_get(v___x_4186_, 0);
                            crate::leanh::lean_inc(v_a_4187_);
                            crate::leanh::lean_dec_ref_known(v___x_4186_, 1);
                            v___x_4188_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                                v_ty_4136_, v_a_3891_, v_a_3894_, v_a_3895_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4188_) == 0 {
                                v_a_4189_ = crate::leanh::lean_ctor_get(v___x_4188_, 0);
                                v_isSharedCheck_4235_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4188_)) as u8;
                                if v_isSharedCheck_4235_ == 0 {
                                    v___x_4191_ = v___x_4188_;
                                    v_isShared_4192_ = v_isSharedCheck_4235_;
                                    state = 39;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4189_);
                                    crate::leanh::lean_dec(v___x_4188_);
                                    v___x_4191_ = crate::leanh::lean_box(0);
                                    v_isShared_4192_ = v_isSharedCheck_4235_;
                                    state = 39;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4187_);
                                crate::leanh::lean_dec_ref(v_k_4137_);
                                crate::leanh::lean_dec(v_y_4135_);
                                crate::leanh::lean_dec(v_offset_4134_);
                                crate::leanh::lean_dec(v_i_4133_);
                                return v___x_4188_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_4137_);
                            crate::leanh::lean_dec_ref(v_ty_4136_);
                            crate::leanh::lean_dec(v_y_4135_);
                            crate::leanh::lean_dec(v_offset_4134_);
                            crate::leanh::lean_dec(v_i_4133_);
                            return v___x_4186_;
                        }
                    }
                }
                10 => {
                    v_fvarId_4236_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    crate::leanh::lean_inc(v_fvarId_4236_);
                    v_cidx_4237_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    crate::leanh::lean_inc(v_cidx_4237_);
                    v_k_4238_ = crate::leanh::lean_ctor_get(v_c_3890_, 2);
                    crate::leanh::lean_inc_ref(v_k_4238_);
                    crate::leanh::lean_dec_ref_known(v_c_3890_, 3);
                    v___x_4239_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4236_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4239_) == 0 {
                        v_a_4240_ = crate::leanh::lean_ctor_get(v___x_4239_, 0);
                        v_isSharedCheck_4267_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4239_)) as u8;
                        if v_isSharedCheck_4267_ == 0 {
                            v___x_4242_ = v___x_4239_;
                            v_isShared_4243_ = v_isSharedCheck_4267_;
                            state = 45;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4240_);
                            crate::leanh::lean_dec(v___x_4239_);
                            v___x_4242_ = crate::leanh::lean_box(0);
                            v_isShared_4243_ = v_isSharedCheck_4267_;
                            state = 45;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_4238_);
                        crate::leanh::lean_dec(v_cidx_4237_);
                        return v___x_4239_;
                    }
                }
                11 => {
                    v_fvarId_4268_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    crate::leanh::lean_inc(v_fvarId_4268_);
                    v_n_4269_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    crate::leanh::lean_inc(v_n_4269_);
                    v_check_4270_ = crate::leanh::lean_ctor_get_uint8(
                        v_c_3890_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_4271_ = crate::leanh::lean_ctor_get_uint8(
                        v_c_3890_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_4272_ = crate::leanh::lean_ctor_get(v_c_3890_, 2);
                    crate::leanh::lean_inc_ref(v_k_4272_);
                    crate::leanh::lean_dec_ref_known(v_c_3890_, 3);
                    if v_persistent_4271_ == 0 {
                        v___x_4344_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20;
                        v___y_4341_ = v___x_4344_;
                        state = 58;
                        continue;
                    } else {
                        v___x_4345_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__35;
                        v___y_4341_ = v___x_4345_;
                        state = 58;
                        continue;
                    }
                }
                12 => {
                    v_fvarId_4346_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    crate::leanh::lean_inc(v_fvarId_4346_);
                    v_n_4347_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    crate::leanh::lean_inc(v_n_4347_);
                    v_check_4348_ = crate::leanh::lean_ctor_get_uint8(
                        v_c_3890_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_4349_ = crate::leanh::lean_ctor_get_uint8(
                        v_c_3890_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_4350_ = crate::leanh::lean_ctor_get(v_c_3890_, 2);
                    crate::leanh::lean_inc(v_objs_x3f_4350_);
                    v_k_4351_ = crate::leanh::lean_ctor_get(v_c_3890_, 3);
                    crate::leanh::lean_inc_ref(v_k_4351_);
                    crate::leanh::lean_dec_ref_known(v_c_3890_, 4);
                    if v_persistent_4349_ == 0 {
                        v_ann_4445_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20;
                        v_ann_4437_ = v_ann_4445_;
                        v___y_4438_ = v_a_3891_;
                        v___y_4439_ = v_a_3892_;
                        v___y_4440_ = v_a_3893_;
                        v___y_4441_ = v_a_3894_;
                        v___y_4442_ = v_a_3895_;
                        state = 69;
                        continue;
                    } else {
                        v_ann_4446_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__35;
                        v_ann_4437_ = v_ann_4446_;
                        v___y_4438_ = v_a_3891_;
                        v___y_4439_ = v_a_3892_;
                        v___y_4440_ = v_a_3893_;
                        v___y_4441_ = v_a_3894_;
                        v___y_4442_ = v_a_3895_;
                        state = 69;
                        continue;
                    }
                }
                _ => {
                    v_fvarId_4447_ = crate::leanh::lean_ctor_get(v_c_3890_, 0);
                    v_k_4448_ = crate::leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_4472_ = (!crate::leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_4472_ == 0 {
                        v___x_4450_ = v_c_3890_;
                        v_isShared_4451_ = v_isSharedCheck_4472_;
                        state = 70;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_4448_);
                        crate::leanh::lean_inc(v_fvarId_4447_);
                        crate::leanh::lean_dec(v_c_3890_);
                        v___x_4450_ = crate::leanh::lean_box(0);
                        v_isShared_4451_ = v_isSharedCheck_4472_;
                        state = 70;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3902_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(
                    v_pu_3889_,
                    v_decl_3897_,
                    v_a_3891_,
                    v_a_3892_,
                    v_a_3893_,
                    v_a_3894_,
                    v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_3902_) == 0 {
                    v_a_3903_ = crate::leanh::lean_ctor_get(v___x_3902_, 0);
                    crate::leanh::lean_inc(v_a_3903_);
                    crate::leanh::lean_dec_ref_known(v___x_3902_, 1);
                    v___x_3904_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3889_, v_k_3898_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3904_) == 0 {
                        v_a_3905_ = crate::leanh::lean_ctor_get(v___x_3904_, 0);
                        v_isSharedCheck_3919_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3904_)) as u8;
                        if v_isSharedCheck_3919_ == 0 {
                            v___x_3907_ = v___x_3904_;
                            v_isShared_3908_ = v_isSharedCheck_3919_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3905_);
                            crate::leanh::lean_dec(v___x_3904_);
                            v___x_3907_ = crate::leanh::lean_box(0);
                            v_isShared_3908_ = v_isSharedCheck_3919_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3903_);
                        crate::leanh::lean_del_object(v___x_3900_);
                        return v___x_3904_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3900_);
                    crate::leanh::lean_dec_ref(v_k_3898_);
                    return v___x_3902_;
                }
            }
            2 => {
                v___x_3909_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                if v_isShared_3901_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3900_, 5);
                    crate::leanh::lean_ctor_set(v___x_3900_, 1, v___x_3909_);
                    crate::leanh::lean_ctor_set(v___x_3900_, 0, v_a_3903_);
                    v___x_3911_ = v___x_3900_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3918_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3918_, 1, v___x_3909_);
                    v___x_3911_ = v_reuseFailAlloc_3918_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3912_ = crate::leanh::lean_box(1);
                v___x_3913_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3913_, 0, v___x_3911_);
                crate::leanh::lean_ctor_set(v___x_3913_, 1, v___x_3912_);
                v___x_3914_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3914_, 0, v___x_3913_);
                crate::leanh::lean_ctor_set(v___x_3914_, 1, v_a_3905_);
                if v_isShared_3908_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3907_, 0, v___x_3914_);
                    v___x_3916_ = v___x_3907_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
                    v___x_3916_ = v_reuseFailAlloc_3917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3916_;
            }
            5 => {
                v___x_3926_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(
                    v_pu_3889_,
                    v_decl_3921_,
                    v_a_3891_,
                    v_a_3892_,
                    v_a_3893_,
                    v_a_3894_,
                    v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_3926_) == 0 {
                    v_a_3927_ = crate::leanh::lean_ctor_get(v___x_3926_, 0);
                    crate::leanh::lean_inc(v_a_3927_);
                    crate::leanh::lean_dec_ref_known(v___x_3926_, 1);
                    v___x_3928_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3889_, v_k_3922_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3928_) == 0 {
                        v_a_3929_ = crate::leanh::lean_ctor_get(v___x_3928_, 0);
                        v_isSharedCheck_3945_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3928_)) as u8;
                        if v_isSharedCheck_3945_ == 0 {
                            v___x_3931_ = v___x_3928_;
                            v_isShared_3932_ = v_isSharedCheck_3945_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3929_);
                            crate::leanh::lean_dec(v___x_3928_);
                            v___x_3931_ = crate::leanh::lean_box(0);
                            v_isShared_3932_ = v_isSharedCheck_3945_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3927_);
                        crate::leanh::lean_del_object(v___x_3924_);
                        return v___x_3928_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3924_);
                    crate::leanh::lean_dec_ref(v_k_3922_);
                    return v___x_3926_;
                }
            }
            6 => {
                v___x_3933_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__3;
                if v_isShared_3925_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3924_, 5);
                    crate::leanh::lean_ctor_set(v___x_3924_, 1, v_a_3927_);
                    crate::leanh::lean_ctor_set(v___x_3924_, 0, v___x_3933_);
                    v___x_3935_ = v___x_3924_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3944_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_a_3927_);
                    v___x_3935_ = v_reuseFailAlloc_3944_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3936_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_3937_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3937_, 0, v___x_3935_);
                crate::leanh::lean_ctor_set(v___x_3937_, 1, v___x_3936_);
                v___x_3938_ = crate::leanh::lean_box(1);
                v___x_3939_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3939_, 0, v___x_3937_);
                crate::leanh::lean_ctor_set(v___x_3939_, 1, v___x_3938_);
                v___x_3940_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3940_, 0, v___x_3939_);
                crate::leanh::lean_ctor_set(v___x_3940_, 1, v_a_3929_);
                if v_isShared_3932_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3931_, 0, v___x_3940_);
                    v___x_3942_ = v___x_3931_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3943_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
                    v___x_3942_ = v_reuseFailAlloc_3943_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3942_;
            }
            9 => {
                v___x_3952_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(
                    v_pu_3889_,
                    v_decl_3947_,
                    v_a_3891_,
                    v_a_3892_,
                    v_a_3893_,
                    v_a_3894_,
                    v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_3952_) == 0 {
                    v_a_3953_ = crate::leanh::lean_ctor_get(v___x_3952_, 0);
                    crate::leanh::lean_inc(v_a_3953_);
                    crate::leanh::lean_dec_ref_known(v___x_3952_, 1);
                    v___x_3954_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3889_, v_k_3948_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3954_) == 0 {
                        v_a_3955_ = crate::leanh::lean_ctor_get(v___x_3954_, 0);
                        v_isSharedCheck_3971_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3954_)) as u8;
                        if v_isSharedCheck_3971_ == 0 {
                            v___x_3957_ = v___x_3954_;
                            v_isShared_3958_ = v_isSharedCheck_3971_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3955_);
                            crate::leanh::lean_dec(v___x_3954_);
                            v___x_3957_ = crate::leanh::lean_box(0);
                            v_isShared_3958_ = v_isSharedCheck_3971_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3953_);
                        crate::leanh::lean_del_object(v___x_3950_);
                        return v___x_3954_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3950_);
                    crate::leanh::lean_dec_ref(v_k_3948_);
                    return v___x_3952_;
                }
            }
            10 => {
                v___x_3959_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__5;
                if v_isShared_3951_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3950_, 5);
                    crate::leanh::lean_ctor_set(v___x_3950_, 1, v_a_3953_);
                    crate::leanh::lean_ctor_set(v___x_3950_, 0, v___x_3959_);
                    v___x_3961_ = v___x_3950_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3970_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_a_3953_);
                    v___x_3961_ = v_reuseFailAlloc_3970_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3962_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_3963_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3963_, 0, v___x_3961_);
                crate::leanh::lean_ctor_set(v___x_3963_, 1, v___x_3962_);
                v___x_3964_ = crate::leanh::lean_box(1);
                v___x_3965_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3965_, 0, v___x_3963_);
                crate::leanh::lean_ctor_set(v___x_3965_, 1, v___x_3964_);
                v___x_3966_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3966_, 0, v___x_3965_);
                crate::leanh::lean_ctor_set(v___x_3966_, 1, v_a_3955_);
                if v_isShared_3958_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3957_, 0, v___x_3966_);
                    v___x_3968_ = v___x_3957_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
                    v___x_3968_ = v_reuseFailAlloc_3969_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3968_;
            }
            13 => {
                v___x_3978_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                    v_fvarId_3973_,
                    v_a_3892_,
                    v_a_3893_,
                    v_a_3894_,
                    v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_3978_) == 0 {
                    v_a_3979_ = crate::leanh::lean_ctor_get(v___x_3978_, 0);
                    crate::leanh::lean_inc(v_a_3979_);
                    crate::leanh::lean_dec_ref_known(v___x_3978_, 1);
                    v___x_3980_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                        v_pu_3889_,
                        v_args_3974_,
                        v_a_3891_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    crate::leanh::lean_dec_ref(v_args_3974_);
                    if crate::leanh::lean_obj_tag(v___x_3980_) == 0 {
                        v_a_3981_ = crate::leanh::lean_ctor_get(v___x_3980_, 0);
                        v_isSharedCheck_3993_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3980_)) as u8;
                        if v_isSharedCheck_3993_ == 0 {
                            v___x_3983_ = v___x_3980_;
                            v_isShared_3984_ = v_isSharedCheck_3993_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3981_);
                            crate::leanh::lean_dec(v___x_3980_);
                            v___x_3983_ = crate::leanh::lean_box(0);
                            v_isShared_3984_ = v_isSharedCheck_3993_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3979_);
                        crate::leanh::lean_del_object(v___x_3976_);
                        return v___x_3980_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3976_);
                    crate::leanh::lean_dec_ref(v_args_3974_);
                    return v___x_3978_;
                }
            }
            14 => {
                v___x_3985_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__7;
                if v_isShared_3977_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3976_, 5);
                    crate::leanh::lean_ctor_set(v___x_3976_, 1, v_a_3979_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 0, v___x_3985_);
                    v___x_3987_ = v___x_3976_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3992_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_a_3979_);
                    v___x_3987_ = v_reuseFailAlloc_3992_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3988_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3988_, 0, v___x_3987_);
                crate::leanh::lean_ctor_set(v___x_3988_, 1, v_a_3981_);
                if v_isShared_3984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3983_, 0, v___x_3988_);
                    v___x_3990_ = v___x_3983_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3991_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3988_);
                    v___x_3990_ = v_reuseFailAlloc_3991_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3990_;
            }
            17 => {
                v___x_4011_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__9;
                v___x_4012_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4012_, 0, v___x_4011_);
                crate::leanh::lean_ctor_set(v___x_4012_, 1, v_a_4000_);
                v___x_4013_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_4014_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4014_, 0, v___x_4012_);
                crate::leanh::lean_ctor_set(v___x_4014_, 1, v___x_4013_);
                v___x_4015_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4015_, 0, v___x_4014_);
                crate::leanh::lean_ctor_set(v___x_4015_, 1, v_a_4002_);
                v___x_4016_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4016_, 0, v___x_4015_);
                crate::leanh::lean_ctor_set(v___x_4016_, 1, v_a_4007_);
                if v_isShared_4010_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4009_, 0, v___x_4016_);
                    v___x_4018_ = v___x_4009_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4018_;
            }
            19 => {
                v___x_4027_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__11;
                v___x_4028_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4028_, 0, v___x_4027_);
                crate::leanh::lean_ctor_set(v___x_4028_, 1, v_a_4023_);
                if v_isShared_4026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4025_, 0, v___x_4028_);
                    v___x_4030_ = v___x_4025_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
                    v___x_4030_ = v_reuseFailAlloc_4031_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4030_;
            }
            21 => {
                v_options_4037_ = crate::leanh::lean_ctor_get(v_a_3894_, 2);
                v___x_4038_ = l_Lean_pp_all;
                v___x_4039_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                    v_options_4037_,
                    v___x_4038_,
                );
                if v___x_4039_ == 0 {
                    crate::leanh::lean_dec_ref(v_type_4033_);
                    v___x_4040_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__13;
                    if v_isShared_4036_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4035_, 0);
                        crate::leanh::lean_ctor_set(v___x_4035_, 0, v___x_4040_);
                        v___x_4042_ = v___x_4035_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_4043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4040_);
                        v___x_4042_ = v_reuseFailAlloc_4043_;
                        state = 22;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4035_);
                    v___x_4044_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                        v_type_4033_,
                        v_a_3891_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4044_) == 0 {
                        v_a_4045_ = crate::leanh::lean_ctor_get(v___x_4044_, 0);
                        v_isSharedCheck_4054_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4044_)) as u8;
                        if v_isSharedCheck_4054_ == 0 {
                            v___x_4047_ = v___x_4044_;
                            v_isShared_4048_ = v_isSharedCheck_4054_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4045_);
                            crate::leanh::lean_dec(v___x_4044_);
                            v___x_4047_ = crate::leanh::lean_box(0);
                            v_isShared_4048_ = v_isSharedCheck_4054_;
                            state = 23;
                            continue;
                        }
                    } else {
                        return v___x_4044_;
                    }
                }
            }
            22 => {
                return v___x_4042_;
            }
            23 => {
                v___x_4049_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__15;
                v___x_4050_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4050_, 0, v___x_4049_);
                crate::leanh::lean_ctor_set(v___x_4050_, 1, v_a_4045_);
                if v_isShared_4048_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4047_, 0, v___x_4050_);
                    v___x_4052_ = v___x_4047_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4053_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
                    v___x_4052_ = v_reuseFailAlloc_4053_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4052_;
            }
            25 => {
                v___x_4067_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4059_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4067_) == 0 {
                    v_a_4068_ = crate::leanh::lean_ctor_get(v___x_4067_, 0);
                    v_isSharedCheck_4092_ = (!crate::leanh::lean_is_exclusive(v___x_4067_)) as u8;
                    if v_isSharedCheck_4092_ == 0 {
                        v___x_4070_ = v___x_4067_;
                        v_isShared_4071_ = v_isSharedCheck_4092_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4068_);
                        crate::leanh::lean_dec(v___x_4067_);
                        v___x_4070_ = crate::leanh::lean_box(0);
                        v_isShared_4071_ = v_isSharedCheck_4092_;
                        state = 26;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4065_);
                    crate::leanh::lean_dec(v_a_4063_);
                    crate::leanh::lean_dec(v_a_4061_);
                    crate::leanh::lean_dec(v_i_4057_);
                    return v___x_4067_;
                }
            }
            26 => {
                v___x_4072_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__17;
                v___x_4073_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4073_, 0, v___x_4072_);
                crate::leanh::lean_ctor_set(v___x_4073_, 1, v_a_4061_);
                v___x_4074_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__19;
                v___x_4075_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4075_, 0, v___x_4073_);
                crate::leanh::lean_ctor_set(v___x_4075_, 1, v___x_4074_);
                v___x_4076_ = l_Nat_reprFast(v_i_4057_);
                if v_isShared_4066_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4065_, 3);
                    crate::leanh::lean_ctor_set(v___x_4065_, 0, v___x_4076_);
                    v___x_4078_ = v___x_4065_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4076_);
                    v___x_4078_ = v_reuseFailAlloc_4091_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_4079_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4079_, 0, v___x_4075_);
                crate::leanh::lean_ctor_set(v___x_4079_, 1, v___x_4078_);
                v___x_4080_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__21;
                v___x_4081_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4081_, 0, v___x_4079_);
                crate::leanh::lean_ctor_set(v___x_4081_, 1, v___x_4080_);
                v___x_4082_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4082_, 0, v___x_4081_);
                crate::leanh::lean_ctor_set(v___x_4082_, 1, v_a_4063_);
                v___x_4083_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4084_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4084_, 0, v___x_4082_);
                crate::leanh::lean_ctor_set(v___x_4084_, 1, v___x_4083_);
                v___x_4085_ = crate::leanh::lean_box(1);
                v___x_4086_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4086_, 0, v___x_4084_);
                crate::leanh::lean_ctor_set(v___x_4086_, 1, v___x_4085_);
                v___x_4087_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4087_, 0, v___x_4086_);
                crate::leanh::lean_ctor_set(v___x_4087_, 1, v_a_4068_);
                if v_isShared_4071_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4070_, 0, v___x_4087_);
                    v___x_4089_ = v___x_4070_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4090_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
                    v___x_4089_ = v_reuseFailAlloc_4090_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4089_;
            }
            29 => {
                v___x_4105_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4097_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4105_) == 0 {
                    v_a_4106_ = crate::leanh::lean_ctor_get(v___x_4105_, 0);
                    v_isSharedCheck_4130_ = (!crate::leanh::lean_is_exclusive(v___x_4105_)) as u8;
                    if v_isSharedCheck_4130_ == 0 {
                        v___x_4108_ = v___x_4105_;
                        v_isShared_4109_ = v_isSharedCheck_4130_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4106_);
                        crate::leanh::lean_dec(v___x_4105_);
                        v___x_4108_ = crate::leanh::lean_box(0);
                        v_isShared_4109_ = v_isSharedCheck_4130_;
                        state = 30;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4103_);
                    crate::leanh::lean_dec(v_a_4101_);
                    crate::leanh::lean_dec(v_a_4099_);
                    crate::leanh::lean_dec(v_i_4095_);
                    return v___x_4105_;
                }
            }
            30 => {
                v___x_4110_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__23;
                v___x_4111_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4111_, 0, v___x_4110_);
                crate::leanh::lean_ctor_set(v___x_4111_, 1, v_a_4099_);
                v___x_4112_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1;
                v___x_4113_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4113_, 0, v___x_4111_);
                crate::leanh::lean_ctor_set(v___x_4113_, 1, v___x_4112_);
                v___x_4114_ = l_Nat_reprFast(v_i_4095_);
                if v_isShared_4104_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4103_, 3);
                    crate::leanh::lean_ctor_set(v___x_4103_, 0, v___x_4114_);
                    v___x_4116_ = v___x_4103_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4129_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4114_);
                    v___x_4116_ = v_reuseFailAlloc_4129_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_4117_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4117_, 0, v___x_4113_);
                crate::leanh::lean_ctor_set(v___x_4117_, 1, v___x_4116_);
                v___x_4118_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__21;
                v___x_4119_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4119_, 0, v___x_4117_);
                crate::leanh::lean_ctor_set(v___x_4119_, 1, v___x_4118_);
                v___x_4120_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4120_, 0, v___x_4119_);
                crate::leanh::lean_ctor_set(v___x_4120_, 1, v_a_4101_);
                v___x_4121_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4122_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4122_, 0, v___x_4120_);
                crate::leanh::lean_ctor_set(v___x_4122_, 1, v___x_4121_);
                v___x_4123_ = crate::leanh::lean_box(1);
                v___x_4124_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4124_, 0, v___x_4122_);
                crate::leanh::lean_ctor_set(v___x_4124_, 1, v___x_4123_);
                v___x_4125_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4125_, 0, v___x_4124_);
                crate::leanh::lean_ctor_set(v___x_4125_, 1, v_a_4106_);
                if v_isShared_4109_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4108_, 0, v___x_4125_);
                    v___x_4127_ = v___x_4108_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
                    v___x_4127_ = v_reuseFailAlloc_4128_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4127_;
            }
            33 => {
                v___x_4146_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                    v_y_4135_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4146_) == 0 {
                    v_a_4147_ = crate::leanh::lean_ctor_get(v___x_4146_, 0);
                    v_isSharedCheck_4184_ = (!crate::leanh::lean_is_exclusive(v___x_4146_)) as u8;
                    if v_isSharedCheck_4184_ == 0 {
                        v___x_4149_ = v___x_4146_;
                        v_isShared_4150_ = v_isSharedCheck_4184_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4147_);
                        crate::leanh::lean_dec(v___x_4146_);
                        v___x_4149_ = crate::leanh::lean_box(0);
                        v_isShared_4150_ = v_isSharedCheck_4184_;
                        state = 34;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4144_);
                    crate::leanh::lean_dec(v_a_4142_);
                    crate::leanh::lean_dec_ref(v_k_4137_);
                    crate::leanh::lean_dec(v_offset_4134_);
                    crate::leanh::lean_dec(v_i_4133_);
                    return v___x_4146_;
                }
            }
            34 => {
                v___x_4151_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4137_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4151_) == 0 {
                    v_a_4152_ = crate::leanh::lean_ctor_get(v___x_4151_, 0);
                    v_isSharedCheck_4183_ = (!crate::leanh::lean_is_exclusive(v___x_4151_)) as u8;
                    if v_isSharedCheck_4183_ == 0 {
                        v___x_4154_ = v___x_4151_;
                        v_isShared_4155_ = v_isSharedCheck_4183_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4152_);
                        crate::leanh::lean_dec(v___x_4151_);
                        v___x_4154_ = crate::leanh::lean_box(0);
                        v_isShared_4155_ = v_isSharedCheck_4183_;
                        state = 35;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4149_);
                    crate::leanh::lean_dec(v_a_4147_);
                    crate::leanh::lean_del_object(v___x_4144_);
                    crate::leanh::lean_dec(v_a_4142_);
                    crate::leanh::lean_dec(v_offset_4134_);
                    crate::leanh::lean_dec(v_i_4133_);
                    return v___x_4151_;
                }
            }
            35 => {
                v___x_4156_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__25;
                v___x_4157_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4157_, 0, v___x_4156_);
                crate::leanh::lean_ctor_set(v___x_4157_, 1, v_a_4142_);
                v___x_4158_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1;
                v___x_4159_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4159_, 0, v___x_4157_);
                crate::leanh::lean_ctor_set(v___x_4159_, 1, v___x_4158_);
                v___x_4160_ = l_Nat_reprFast(v_i_4133_);
                if v_isShared_4150_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4149_, 3);
                    crate::leanh::lean_ctor_set(v___x_4149_, 0, v___x_4160_);
                    v___x_4162_ = v___x_4149_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4182_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4160_);
                    v___x_4162_ = v_reuseFailAlloc_4182_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___x_4163_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4163_, 0, v___x_4159_);
                crate::leanh::lean_ctor_set(v___x_4163_, 1, v___x_4162_);
                v___x_4164_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11;
                v___x_4165_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4165_, 0, v___x_4163_);
                crate::leanh::lean_ctor_set(v___x_4165_, 1, v___x_4164_);
                v___x_4166_ = l_Nat_reprFast(v_offset_4134_);
                if v_isShared_4145_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4144_, 3);
                    crate::leanh::lean_ctor_set(v___x_4144_, 0, v___x_4166_);
                    v___x_4168_ = v___x_4144_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4181_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4166_);
                    v___x_4168_ = v_reuseFailAlloc_4181_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_4169_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4169_, 0, v___x_4165_);
                crate::leanh::lean_ctor_set(v___x_4169_, 1, v___x_4168_);
                v___x_4170_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__21;
                v___x_4171_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4171_, 0, v___x_4169_);
                crate::leanh::lean_ctor_set(v___x_4171_, 1, v___x_4170_);
                v___x_4172_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4172_, 0, v___x_4171_);
                crate::leanh::lean_ctor_set(v___x_4172_, 1, v_a_4147_);
                v___x_4173_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4174_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4174_, 0, v___x_4172_);
                crate::leanh::lean_ctor_set(v___x_4174_, 1, v___x_4173_);
                v___x_4175_ = crate::leanh::lean_box(1);
                v___x_4176_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4176_, 0, v___x_4174_);
                crate::leanh::lean_ctor_set(v___x_4176_, 1, v___x_4175_);
                v___x_4177_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4177_, 0, v___x_4176_);
                crate::leanh::lean_ctor_set(v___x_4177_, 1, v_a_4152_);
                if v_isShared_4155_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4154_, 0, v___x_4177_);
                    v___x_4179_ = v___x_4154_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4177_);
                    v___x_4179_ = v_reuseFailAlloc_4180_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4179_;
            }
            39 => {
                v___x_4193_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                    v_y_4135_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4193_) == 0 {
                    v_a_4194_ = crate::leanh::lean_ctor_get(v___x_4193_, 0);
                    v_isSharedCheck_4234_ = (!crate::leanh::lean_is_exclusive(v___x_4193_)) as u8;
                    if v_isSharedCheck_4234_ == 0 {
                        v___x_4196_ = v___x_4193_;
                        v_isShared_4197_ = v_isSharedCheck_4234_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4194_);
                        crate::leanh::lean_dec(v___x_4193_);
                        v___x_4196_ = crate::leanh::lean_box(0);
                        v_isShared_4197_ = v_isSharedCheck_4234_;
                        state = 40;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4191_);
                    crate::leanh::lean_dec(v_a_4189_);
                    crate::leanh::lean_dec(v_a_4187_);
                    crate::leanh::lean_dec_ref(v_k_4137_);
                    crate::leanh::lean_dec(v_offset_4134_);
                    crate::leanh::lean_dec(v_i_4133_);
                    return v___x_4193_;
                }
            }
            40 => {
                v___x_4198_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4137_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4198_) == 0 {
                    v_a_4199_ = crate::leanh::lean_ctor_get(v___x_4198_, 0);
                    v_isSharedCheck_4233_ = (!crate::leanh::lean_is_exclusive(v___x_4198_)) as u8;
                    if v_isSharedCheck_4233_ == 0 {
                        v___x_4201_ = v___x_4198_;
                        v_isShared_4202_ = v_isSharedCheck_4233_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4199_);
                        crate::leanh::lean_dec(v___x_4198_);
                        v___x_4201_ = crate::leanh::lean_box(0);
                        v_isShared_4202_ = v_isSharedCheck_4233_;
                        state = 41;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4196_);
                    crate::leanh::lean_dec(v_a_4194_);
                    crate::leanh::lean_del_object(v___x_4191_);
                    crate::leanh::lean_dec(v_a_4189_);
                    crate::leanh::lean_dec(v_a_4187_);
                    crate::leanh::lean_dec(v_offset_4134_);
                    crate::leanh::lean_dec(v_i_4133_);
                    return v___x_4198_;
                }
            }
            41 => {
                v___x_4203_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__25;
                v___x_4204_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4204_, 0, v___x_4203_);
                crate::leanh::lean_ctor_set(v___x_4204_, 1, v_a_4187_);
                v___x_4205_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1;
                v___x_4206_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4206_, 0, v___x_4204_);
                crate::leanh::lean_ctor_set(v___x_4206_, 1, v___x_4205_);
                v___x_4207_ = l_Nat_reprFast(v_i_4133_);
                if v_isShared_4197_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4196_, 3);
                    crate::leanh::lean_ctor_set(v___x_4196_, 0, v___x_4207_);
                    v___x_4209_ = v___x_4196_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4207_);
                    v___x_4209_ = v_reuseFailAlloc_4232_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v___x_4210_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4210_, 0, v___x_4206_);
                crate::leanh::lean_ctor_set(v___x_4210_, 1, v___x_4209_);
                v___x_4211_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11;
                v___x_4212_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4212_, 0, v___x_4210_);
                crate::leanh::lean_ctor_set(v___x_4212_, 1, v___x_4211_);
                v___x_4213_ = l_Nat_reprFast(v_offset_4134_);
                if v_isShared_4192_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4191_, 3);
                    crate::leanh::lean_ctor_set(v___x_4191_, 0, v___x_4213_);
                    v___x_4215_ = v___x_4191_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4213_);
                    v___x_4215_ = v_reuseFailAlloc_4231_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_4216_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4216_, 0, v___x_4212_);
                crate::leanh::lean_ctor_set(v___x_4216_, 1, v___x_4215_);
                v___x_4217_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__27;
                v___x_4218_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4218_, 0, v___x_4216_);
                crate::leanh::lean_ctor_set(v___x_4218_, 1, v___x_4217_);
                v___x_4219_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4219_, 0, v___x_4218_);
                crate::leanh::lean_ctor_set(v___x_4219_, 1, v_a_4189_);
                v___x_4220_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
                v___x_4221_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4221_, 0, v___x_4219_);
                crate::leanh::lean_ctor_set(v___x_4221_, 1, v___x_4220_);
                v___x_4222_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4222_, 0, v___x_4221_);
                crate::leanh::lean_ctor_set(v___x_4222_, 1, v_a_4194_);
                v___x_4223_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4224_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4224_, 0, v___x_4222_);
                crate::leanh::lean_ctor_set(v___x_4224_, 1, v___x_4223_);
                v___x_4225_ = crate::leanh::lean_box(1);
                v___x_4226_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4226_, 0, v___x_4224_);
                crate::leanh::lean_ctor_set(v___x_4226_, 1, v___x_4225_);
                v___x_4227_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4226_);
                crate::leanh::lean_ctor_set(v___x_4227_, 1, v_a_4199_);
                if v_isShared_4202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4201_, 0, v___x_4227_);
                    v___x_4229_ = v___x_4201_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4230_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
                    v___x_4229_ = v_reuseFailAlloc_4230_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4229_;
            }
            45 => {
                v___x_4244_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4238_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4244_) == 0 {
                    v_a_4245_ = crate::leanh::lean_ctor_get(v___x_4244_, 0);
                    v_isSharedCheck_4266_ = (!crate::leanh::lean_is_exclusive(v___x_4244_)) as u8;
                    if v_isSharedCheck_4266_ == 0 {
                        v___x_4247_ = v___x_4244_;
                        v_isShared_4248_ = v_isSharedCheck_4266_;
                        state = 46;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4245_);
                        crate::leanh::lean_dec(v___x_4244_);
                        v___x_4247_ = crate::leanh::lean_box(0);
                        v_isShared_4248_ = v_isSharedCheck_4266_;
                        state = 46;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4242_);
                    crate::leanh::lean_dec(v_a_4240_);
                    crate::leanh::lean_dec(v_cidx_4237_);
                    return v___x_4244_;
                }
            }
            46 => {
                v___x_4249_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__29;
                v___x_4250_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4250_, 0, v___x_4249_);
                crate::leanh::lean_ctor_set(v___x_4250_, 1, v_a_4240_);
                v___x_4251_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
                v___x_4252_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4252_, 0, v___x_4250_);
                crate::leanh::lean_ctor_set(v___x_4252_, 1, v___x_4251_);
                v___x_4253_ = l_Nat_reprFast(v_cidx_4237_);
                if v_isShared_4243_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4242_, 3);
                    crate::leanh::lean_ctor_set(v___x_4242_, 0, v___x_4253_);
                    v___x_4255_ = v___x_4242_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4265_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4253_);
                    v___x_4255_ = v_reuseFailAlloc_4265_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                v___x_4256_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4256_, 0, v___x_4252_);
                crate::leanh::lean_ctor_set(v___x_4256_, 1, v___x_4255_);
                v___x_4257_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4258_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4258_, 0, v___x_4256_);
                crate::leanh::lean_ctor_set(v___x_4258_, 1, v___x_4257_);
                v___x_4259_ = crate::leanh::lean_box(1);
                v___x_4260_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4260_, 0, v___x_4258_);
                crate::leanh::lean_ctor_set(v___x_4260_, 1, v___x_4259_);
                v___x_4261_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4261_, 0, v___x_4260_);
                crate::leanh::lean_ctor_set(v___x_4261_, 1, v_a_4245_);
                if v_isShared_4248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4247_, 0, v___x_4261_);
                    v___x_4263_ = v___x_4247_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4261_);
                    v___x_4263_ = v_reuseFailAlloc_4264_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4263_;
            }
            49 => {
                crate::leanh::lean_inc_ref(v___y_4274_);
                v_ann_4276_ = lean_string_append(v___y_4274_, v___y_4275_);
                v___x_4277_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4278_ = lean_nat_dec_eq(v_n_4269_, v___x_4277_);
                if v___x_4278_ == 0 {
                    v___x_4279_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4268_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4279_) == 0 {
                        v_a_4280_ = crate::leanh::lean_ctor_get(v___x_4279_, 0);
                        v_isSharedCheck_4311_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4279_)) as u8;
                        if v_isSharedCheck_4311_ == 0 {
                            v___x_4282_ = v___x_4279_;
                            v_isShared_4283_ = v_isSharedCheck_4311_;
                            state = 50;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4280_);
                            crate::leanh::lean_dec(v___x_4279_);
                            v___x_4282_ = crate::leanh::lean_box(0);
                            v_isShared_4283_ = v_isSharedCheck_4311_;
                            state = 50;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ann_4276_);
                        crate::leanh::lean_dec_ref(v_k_4272_);
                        crate::leanh::lean_dec(v_n_4269_);
                        return v___x_4279_;
                    }
                } else {
                    crate::leanh::lean_dec(v_n_4269_);
                    v___x_4312_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4268_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4312_) == 0 {
                        v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                        v_isSharedCheck_4339_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                        if v_isSharedCheck_4339_ == 0 {
                            v___x_4315_ = v___x_4312_;
                            v_isShared_4316_ = v_isSharedCheck_4339_;
                            state = 54;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4313_);
                            crate::leanh::lean_dec(v___x_4312_);
                            v___x_4315_ = crate::leanh::lean_box(0);
                            v_isShared_4316_ = v_isSharedCheck_4339_;
                            state = 54;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ann_4276_);
                        crate::leanh::lean_dec_ref(v_k_4272_);
                        return v___x_4312_;
                    }
                }
            }
            50 => {
                v___x_4284_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4272_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4284_) == 0 {
                    v_a_4285_ = crate::leanh::lean_ctor_get(v___x_4284_, 0);
                    v_isSharedCheck_4310_ = (!crate::leanh::lean_is_exclusive(v___x_4284_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4287_ = v___x_4284_;
                        v_isShared_4288_ = v_isSharedCheck_4310_;
                        state = 51;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4285_);
                        crate::leanh::lean_dec(v___x_4284_);
                        v___x_4287_ = crate::leanh::lean_box(0);
                        v_isShared_4288_ = v_isSharedCheck_4310_;
                        state = 51;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4282_);
                    crate::leanh::lean_dec(v_a_4280_);
                    crate::leanh::lean_dec_ref(v_ann_4276_);
                    crate::leanh::lean_dec(v_n_4269_);
                    return v___x_4284_;
                }
            }
            51 => {
                v___x_4289_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__31;
                v___x_4290_ = l_Nat_reprFast(v_n_4269_);
                if v_isShared_4283_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4282_, 3);
                    crate::leanh::lean_ctor_set(v___x_4282_, 0, v___x_4290_);
                    v___x_4292_ = v___x_4282_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4290_);
                    v___x_4292_ = v_reuseFailAlloc_4309_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                v___x_4293_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4293_, 0, v___x_4289_);
                crate::leanh::lean_ctor_set(v___x_4293_, 1, v___x_4292_);
                v___x_4294_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3;
                v___x_4295_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4295_, 0, v___x_4293_);
                crate::leanh::lean_ctor_set(v___x_4295_, 1, v___x_4294_);
                v___x_4296_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4296_, 0, v_ann_4276_);
                v___x_4297_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4297_, 0, v___x_4295_);
                crate::leanh::lean_ctor_set(v___x_4297_, 1, v___x_4296_);
                v___x_4298_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_4299_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4299_, 0, v___x_4297_);
                crate::leanh::lean_ctor_set(v___x_4299_, 1, v___x_4298_);
                v___x_4300_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4300_, 0, v___x_4299_);
                crate::leanh::lean_ctor_set(v___x_4300_, 1, v_a_4280_);
                v___x_4301_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4302_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4302_, 0, v___x_4300_);
                crate::leanh::lean_ctor_set(v___x_4302_, 1, v___x_4301_);
                v___x_4303_ = crate::leanh::lean_box(1);
                v___x_4304_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4304_, 0, v___x_4302_);
                crate::leanh::lean_ctor_set(v___x_4304_, 1, v___x_4303_);
                v___x_4305_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4305_, 0, v___x_4304_);
                crate::leanh::lean_ctor_set(v___x_4305_, 1, v_a_4285_);
                if v_isShared_4288_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4287_, 0, v___x_4305_);
                    v___x_4307_ = v___x_4287_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
                    v___x_4307_ = v_reuseFailAlloc_4308_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_4307_;
            }
            54 => {
                v___x_4317_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4272_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4317_) == 0 {
                    v_a_4318_ = crate::leanh::lean_ctor_get(v___x_4317_, 0);
                    v_isSharedCheck_4338_ = (!crate::leanh::lean_is_exclusive(v___x_4317_)) as u8;
                    if v_isSharedCheck_4338_ == 0 {
                        v___x_4320_ = v___x_4317_;
                        v_isShared_4321_ = v_isSharedCheck_4338_;
                        state = 55;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4318_);
                        crate::leanh::lean_dec(v___x_4317_);
                        v___x_4320_ = crate::leanh::lean_box(0);
                        v_isShared_4321_ = v_isSharedCheck_4338_;
                        state = 55;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4315_);
                    crate::leanh::lean_dec(v_a_4313_);
                    crate::leanh::lean_dec_ref(v_ann_4276_);
                    return v___x_4317_;
                }
            }
            55 => {
                v___x_4322_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__33;
                if v_isShared_4316_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4315_, 3);
                    crate::leanh::lean_ctor_set(v___x_4315_, 0, v_ann_4276_);
                    v___x_4324_ = v___x_4315_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_ann_4276_);
                    v___x_4324_ = v_reuseFailAlloc_4337_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v___x_4325_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4325_, 0, v___x_4322_);
                crate::leanh::lean_ctor_set(v___x_4325_, 1, v___x_4324_);
                v___x_4326_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_4327_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4327_, 0, v___x_4325_);
                crate::leanh::lean_ctor_set(v___x_4327_, 1, v___x_4326_);
                v___x_4328_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4328_, 0, v___x_4327_);
                crate::leanh::lean_ctor_set(v___x_4328_, 1, v_a_4313_);
                v___x_4329_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4330_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4330_, 0, v___x_4328_);
                crate::leanh::lean_ctor_set(v___x_4330_, 1, v___x_4329_);
                v___x_4331_ = crate::leanh::lean_box(1);
                v___x_4332_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4332_, 0, v___x_4330_);
                crate::leanh::lean_ctor_set(v___x_4332_, 1, v___x_4331_);
                v___x_4333_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4333_, 0, v___x_4332_);
                crate::leanh::lean_ctor_set(v___x_4333_, 1, v_a_4318_);
                if v_isShared_4321_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4320_, 0, v___x_4333_);
                    v___x_4335_ = v___x_4320_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4336_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4333_);
                    v___x_4335_ = v_reuseFailAlloc_4336_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_4335_;
            }
            58 => {
                if v_check_4270_ == 0 {
                    v___x_4342_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__34;
                    v___y_4274_ = v___y_4341_;
                    v___y_4275_ = v___x_4342_;
                    state = 49;
                    continue;
                } else {
                    v___x_4343_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20;
                    v___y_4274_ = v___y_4341_;
                    v___y_4275_ = v___x_4343_;
                    state = 49;
                    continue;
                }
            }
            59 => {
                v___x_4359_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4360_ = lean_nat_dec_eq(v_n_4347_, v___x_4359_);
                if v___x_4360_ == 0 {
                    v___x_4361_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4346_,
                        v___y_4355_,
                        v___y_4356_,
                        v___y_4357_,
                        v___y_4358_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4361_) == 0 {
                        v_a_4362_ = crate::leanh::lean_ctor_get(v___x_4361_, 0);
                        v_isSharedCheck_4393_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4361_)) as u8;
                        if v_isSharedCheck_4393_ == 0 {
                            v___x_4364_ = v___x_4361_;
                            v_isShared_4365_ = v_isSharedCheck_4393_;
                            state = 60;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4362_);
                            crate::leanh::lean_dec(v___x_4361_);
                            v___x_4364_ = crate::leanh::lean_box(0);
                            v_isShared_4365_ = v_isSharedCheck_4393_;
                            state = 60;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ann_4353_);
                        crate::leanh::lean_dec_ref(v_k_4351_);
                        crate::leanh::lean_dec(v_n_4347_);
                        return v___x_4361_;
                    }
                } else {
                    crate::leanh::lean_dec(v_n_4347_);
                    v___x_4394_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4346_,
                        v___y_4355_,
                        v___y_4356_,
                        v___y_4357_,
                        v___y_4358_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4394_) == 0 {
                        v_a_4395_ = crate::leanh::lean_ctor_get(v___x_4394_, 0);
                        v_isSharedCheck_4421_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4394_)) as u8;
                        if v_isSharedCheck_4421_ == 0 {
                            v___x_4397_ = v___x_4394_;
                            v_isShared_4398_ = v_isSharedCheck_4421_;
                            state = 64;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4395_);
                            crate::leanh::lean_dec(v___x_4394_);
                            v___x_4397_ = crate::leanh::lean_box(0);
                            v_isShared_4398_ = v_isSharedCheck_4421_;
                            state = 64;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ann_4353_);
                        crate::leanh::lean_dec_ref(v_k_4351_);
                        return v___x_4394_;
                    }
                }
            }
            60 => {
                v___x_4366_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_,
                    v_k_4351_,
                    v___y_4354_,
                    v___y_4355_,
                    v___y_4356_,
                    v___y_4357_,
                    v___y_4358_,
                );
                if crate::leanh::lean_obj_tag(v___x_4366_) == 0 {
                    v_a_4367_ = crate::leanh::lean_ctor_get(v___x_4366_, 0);
                    v_isSharedCheck_4392_ = (!crate::leanh::lean_is_exclusive(v___x_4366_)) as u8;
                    if v_isSharedCheck_4392_ == 0 {
                        v___x_4369_ = v___x_4366_;
                        v_isShared_4370_ = v_isSharedCheck_4392_;
                        state = 61;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4367_);
                        crate::leanh::lean_dec(v___x_4366_);
                        v___x_4369_ = crate::leanh::lean_box(0);
                        v_isShared_4370_ = v_isSharedCheck_4392_;
                        state = 61;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4364_);
                    crate::leanh::lean_dec(v_a_4362_);
                    crate::leanh::lean_dec_ref(v_ann_4353_);
                    crate::leanh::lean_dec(v_n_4347_);
                    return v___x_4366_;
                }
            }
            61 => {
                v___x_4371_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__37;
                v___x_4372_ = l_Nat_reprFast(v_n_4347_);
                if v_isShared_4365_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4364_, 3);
                    crate::leanh::lean_ctor_set(v___x_4364_, 0, v___x_4372_);
                    v___x_4374_ = v___x_4364_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_4391_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4372_);
                    v___x_4374_ = v_reuseFailAlloc_4391_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                v___x_4375_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4375_, 0, v___x_4371_);
                crate::leanh::lean_ctor_set(v___x_4375_, 1, v___x_4374_);
                v___x_4376_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3;
                v___x_4377_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4377_, 0, v___x_4375_);
                crate::leanh::lean_ctor_set(v___x_4377_, 1, v___x_4376_);
                v___x_4378_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4378_, 0, v_ann_4353_);
                v___x_4379_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4379_, 0, v___x_4377_);
                crate::leanh::lean_ctor_set(v___x_4379_, 1, v___x_4378_);
                v___x_4380_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_4381_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4381_, 0, v___x_4379_);
                crate::leanh::lean_ctor_set(v___x_4381_, 1, v___x_4380_);
                v___x_4382_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4382_, 0, v___x_4381_);
                crate::leanh::lean_ctor_set(v___x_4382_, 1, v_a_4362_);
                v___x_4383_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4384_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4384_, 0, v___x_4382_);
                crate::leanh::lean_ctor_set(v___x_4384_, 1, v___x_4383_);
                v___x_4385_ = crate::leanh::lean_box(1);
                v___x_4386_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4386_, 0, v___x_4384_);
                crate::leanh::lean_ctor_set(v___x_4386_, 1, v___x_4385_);
                v___x_4387_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4387_, 0, v___x_4386_);
                crate::leanh::lean_ctor_set(v___x_4387_, 1, v_a_4367_);
                if v_isShared_4370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4369_, 0, v___x_4387_);
                    v___x_4389_ = v___x_4369_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_4390_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4387_);
                    v___x_4389_ = v_reuseFailAlloc_4390_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_4389_;
            }
            64 => {
                v___x_4399_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_,
                    v_k_4351_,
                    v___y_4354_,
                    v___y_4355_,
                    v___y_4356_,
                    v___y_4357_,
                    v___y_4358_,
                );
                if crate::leanh::lean_obj_tag(v___x_4399_) == 0 {
                    v_a_4400_ = crate::leanh::lean_ctor_get(v___x_4399_, 0);
                    v_isSharedCheck_4420_ = (!crate::leanh::lean_is_exclusive(v___x_4399_)) as u8;
                    if v_isSharedCheck_4420_ == 0 {
                        v___x_4402_ = v___x_4399_;
                        v_isShared_4403_ = v_isSharedCheck_4420_;
                        state = 65;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4400_);
                        crate::leanh::lean_dec(v___x_4399_);
                        v___x_4402_ = crate::leanh::lean_box(0);
                        v_isShared_4403_ = v_isSharedCheck_4420_;
                        state = 65;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4397_);
                    crate::leanh::lean_dec(v_a_4395_);
                    crate::leanh::lean_dec_ref(v_ann_4353_);
                    return v___x_4399_;
                }
            }
            65 => {
                v___x_4404_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__39;
                if v_isShared_4398_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4397_, 3);
                    crate::leanh::lean_ctor_set(v___x_4397_, 0, v_ann_4353_);
                    v___x_4406_ = v___x_4397_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_4419_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_ann_4353_);
                    v___x_4406_ = v_reuseFailAlloc_4419_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                v___x_4407_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4407_, 0, v___x_4404_);
                crate::leanh::lean_ctor_set(v___x_4407_, 1, v___x_4406_);
                v___x_4408_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_4409_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4409_, 0, v___x_4407_);
                crate::leanh::lean_ctor_set(v___x_4409_, 1, v___x_4408_);
                v___x_4410_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4410_, 0, v___x_4409_);
                crate::leanh::lean_ctor_set(v___x_4410_, 1, v_a_4395_);
                v___x_4411_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4412_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4412_, 0, v___x_4410_);
                crate::leanh::lean_ctor_set(v___x_4412_, 1, v___x_4411_);
                v___x_4413_ = crate::leanh::lean_box(1);
                v___x_4414_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4414_, 0, v___x_4412_);
                crate::leanh::lean_ctor_set(v___x_4414_, 1, v___x_4413_);
                v___x_4415_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4415_, 0, v___x_4414_);
                crate::leanh::lean_ctor_set(v___x_4415_, 1, v_a_4400_);
                if v_isShared_4403_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4402_, 0, v___x_4415_);
                    v___x_4417_ = v___x_4402_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4418_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
                    v___x_4417_ = v_reuseFailAlloc_4418_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_4417_;
            }
            68 => {
                if crate::leanh::lean_obj_tag(v_objs_x3f_4350_) == 1 {
                    v_val_4429_ = crate::leanh::lean_ctor_get(v_objs_x3f_4350_, 0);
                    crate::leanh::lean_inc(v_val_4429_);
                    crate::leanh::lean_dec_ref_known(v_objs_x3f_4350_, 1);
                    v___x_4430_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0;
                    v___x_4431_ = l_Nat_reprFast(v_val_4429_);
                    v___x_4432_ = lean_string_append(v___x_4430_, v___x_4431_);
                    crate::leanh::lean_dec_ref(v___x_4431_);
                    v___x_4433_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__40;
                    v___x_4434_ = lean_string_append(v___x_4432_, v___x_4433_);
                    v_ann_4435_ = lean_string_append(v_ann_4423_, v___x_4434_);
                    crate::leanh::lean_dec_ref(v___x_4434_);
                    v_ann_4353_ = v_ann_4435_;
                    v___y_4354_ = v___y_4424_;
                    v___y_4355_ = v___y_4425_;
                    v___y_4356_ = v___y_4426_;
                    v___y_4357_ = v___y_4427_;
                    v___y_4358_ = v___y_4428_;
                    state = 59;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_objs_x3f_4350_);
                    v_ann_4353_ = v_ann_4423_;
                    v___y_4354_ = v___y_4424_;
                    v___y_4355_ = v___y_4425_;
                    v___y_4356_ = v___y_4426_;
                    v___y_4357_ = v___y_4427_;
                    v___y_4358_ = v___y_4428_;
                    state = 59;
                    continue;
                }
            }
            69 => {
                if v_check_4348_ == 0 {
                    v___x_4443_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__34;
                    crate::leanh::lean_inc_ref(v_ann_4437_);
                    v_ann_4444_ = lean_string_append(v_ann_4437_, v___x_4443_);
                    v_ann_4423_ = v_ann_4444_;
                    v___y_4424_ = v___y_4438_;
                    v___y_4425_ = v___y_4439_;
                    v___y_4426_ = v___y_4440_;
                    v___y_4427_ = v___y_4441_;
                    v___y_4428_ = v___y_4442_;
                    state = 68;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_ann_4437_);
                    v_ann_4423_ = v_ann_4437_;
                    v___y_4424_ = v___y_4438_;
                    v___y_4425_ = v___y_4439_;
                    v___y_4426_ = v___y_4440_;
                    v___y_4427_ = v___y_4441_;
                    v___y_4428_ = v___y_4442_;
                    state = 68;
                    continue;
                }
            }
            70 => {
                v___x_4452_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                    v_fvarId_4447_,
                    v_a_3892_,
                    v_a_3893_,
                    v_a_3894_,
                    v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4452_) == 0 {
                    v_a_4453_ = crate::leanh::lean_ctor_get(v___x_4452_, 0);
                    crate::leanh::lean_inc(v_a_4453_);
                    crate::leanh::lean_dec_ref_known(v___x_4452_, 1);
                    v___x_4454_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3889_, v_k_4448_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_,
                        v_a_3895_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4454_) == 0 {
                        v_a_4455_ = crate::leanh::lean_ctor_get(v___x_4454_, 0);
                        v_isSharedCheck_4471_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4454_)) as u8;
                        if v_isSharedCheck_4471_ == 0 {
                            v___x_4457_ = v___x_4454_;
                            v_isShared_4458_ = v_isSharedCheck_4471_;
                            state = 71;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4455_);
                            crate::leanh::lean_dec(v___x_4454_);
                            v___x_4457_ = crate::leanh::lean_box(0);
                            v_isShared_4458_ = v_isSharedCheck_4471_;
                            state = 71;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4453_);
                        crate::leanh::lean_del_object(v___x_4450_);
                        return v___x_4454_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4450_);
                    crate::leanh::lean_dec_ref(v_k_4448_);
                    return v___x_4452_;
                }
            }
            71 => {
                v___x_4459_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__42;
                if v_isShared_4451_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4450_, 5);
                    crate::leanh::lean_ctor_set(v___x_4450_, 1, v_a_4453_);
                    crate::leanh::lean_ctor_set(v___x_4450_, 0, v___x_4459_);
                    v___x_4461_ = v___x_4450_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 1, v_a_4453_);
                    v___x_4461_ = v_reuseFailAlloc_4470_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                v___x_4462_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4463_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4463_, 0, v___x_4461_);
                crate::leanh::lean_ctor_set(v___x_4463_, 1, v___x_4462_);
                v___x_4464_ = crate::leanh::lean_box(1);
                v___x_4465_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4465_, 0, v___x_4463_);
                crate::leanh::lean_ctor_set(v___x_4465_, 1, v___x_4464_);
                v___x_4466_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4466_, 0, v___x_4465_);
                crate::leanh::lean_ctor_set(v___x_4466_, 1, v_a_4455_);
                if v_isShared_4458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4457_, 0, v___x_4466_);
                    v___x_4468_ = v___x_4457_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_4469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
                    v___x_4468_ = v_reuseFailAlloc_4469_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_4468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppFunDecl(
    mut v_pu_4473_: u8,
    mut v_funDecl_4474_: *mut crate::leanh::LeanObject,
    mut v_a_4475_: *mut crate::leanh::LeanObject,
    mut v_a_4476_: *mut crate::leanh::LeanObject,
    mut v_a_4477_: *mut crate::leanh::LeanObject,
    mut v_a_4478_: *mut crate::leanh::LeanObject,
    mut v_a_4479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4493_: u8 = 0;
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4498_: u8 = 0;
    let mut v___x_4499_: u8 = 0;
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4515_: u8 = 0;
    let mut v_isSharedCheck_4516_: u8 = 0;
    let mut v_a_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4520_: u8 = 0;
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_binderName_4481_ = crate::leanh::lean_ctor_get(v_funDecl_4474_, 1);
                crate::leanh::lean_inc(v_binderName_4481_);
                v_params_4482_ = crate::leanh::lean_ctor_get(v_funDecl_4474_, 2);
                crate::leanh::lean_inc_ref(v_params_4482_);
                v_type_4483_ = crate::leanh::lean_ctor_get(v_funDecl_4474_, 3);
                crate::leanh::lean_inc_ref(v_type_4483_);
                v_value_4484_ = crate::leanh::lean_ctor_get(v_funDecl_4474_, 4);
                crate::leanh::lean_inc_ref(v_value_4484_);
                crate::leanh::lean_dec_ref(v_funDecl_4474_);
                v___x_4485_ = l_Lean_Compiler_LCNF_PP_ppParams(
                    v_pu_4473_,
                    v_params_4482_,
                    v_a_4475_,
                    v_a_4476_,
                    v_a_4477_,
                    v_a_4478_,
                    v_a_4479_,
                );
                if crate::leanh::lean_obj_tag(v___x_4485_) == 0 {
                    v_a_4486_ = crate::leanh::lean_ctor_get(v___x_4485_, 0);
                    crate::leanh::lean_inc(v_a_4486_);
                    crate::leanh::lean_dec_ref_known(v___x_4485_, 1);
                    v___x_4487_ = l_Lean_Compiler_LCNF_PP_getFunType(
                        v_pu_4473_,
                        v_params_4482_,
                        v_type_4483_,
                        v_a_4478_,
                        v_a_4479_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4487_) == 0 {
                        v_a_4488_ = crate::leanh::lean_ctor_get(v___x_4487_, 0);
                        crate::leanh::lean_inc(v_a_4488_);
                        crate::leanh::lean_dec_ref_known(v___x_4487_, 1);
                        v___x_4489_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                            v_a_4488_, v_a_4475_, v_a_4478_, v_a_4479_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4489_) == 0 {
                            v_a_4490_ = crate::leanh::lean_ctor_get(v___x_4489_, 0);
                            v_isSharedCheck_4516_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4489_)) as u8;
                            if v_isSharedCheck_4516_ == 0 {
                                v___x_4492_ = v___x_4489_;
                                v_isShared_4493_ = v_isSharedCheck_4516_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4490_);
                                crate::leanh::lean_dec(v___x_4489_);
                                v___x_4492_ = crate::leanh::lean_box(0);
                                v_isShared_4493_ = v_isSharedCheck_4516_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4486_);
                            crate::leanh::lean_dec_ref(v_value_4484_);
                            crate::leanh::lean_dec(v_binderName_4481_);
                            return v___x_4489_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4486_);
                        crate::leanh::lean_dec_ref(v_value_4484_);
                        crate::leanh::lean_dec(v_binderName_4481_);
                        v_a_4517_ = crate::leanh::lean_ctor_get(v___x_4487_, 0);
                        v_isSharedCheck_4524_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4487_)) as u8;
                        if v_isSharedCheck_4524_ == 0 {
                            v___x_4519_ = v___x_4487_;
                            v_isShared_4520_ = v_isSharedCheck_4524_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4517_);
                            crate::leanh::lean_dec(v___x_4487_);
                            v___x_4519_ = crate::leanh::lean_box(0);
                            v_isShared_4520_ = v_isSharedCheck_4524_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_4484_);
                    crate::leanh::lean_dec_ref(v_type_4483_);
                    crate::leanh::lean_dec_ref(v_params_4482_);
                    crate::leanh::lean_dec(v_binderName_4481_);
                    return v___x_4485_;
                }
            }
            1 => {
                v___x_4494_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_4473_,
                    v_value_4484_,
                    v_a_4475_,
                    v_a_4476_,
                    v_a_4477_,
                    v_a_4478_,
                    v_a_4479_,
                );
                if crate::leanh::lean_obj_tag(v___x_4494_) == 0 {
                    v_a_4495_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
                    v_isSharedCheck_4515_ = (!crate::leanh::lean_is_exclusive(v___x_4494_)) as u8;
                    if v_isSharedCheck_4515_ == 0 {
                        v___x_4497_ = v___x_4494_;
                        v_isShared_4498_ = v_isSharedCheck_4515_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4495_);
                        crate::leanh::lean_dec(v___x_4494_);
                        v___x_4497_ = crate::leanh::lean_box(0);
                        v_isShared_4498_ = v_isSharedCheck_4515_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4492_);
                    crate::leanh::lean_dec(v_a_4490_);
                    crate::leanh::lean_dec(v_a_4486_);
                    crate::leanh::lean_dec(v_binderName_4481_);
                    return v___x_4494_;
                }
            }
            2 => {
                v___x_4499_ = 1;
                v___x_4500_ = l_Lean_Name_toString(v_binderName_4481_, v___x_4499_);
                if v_isShared_4493_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4492_, 3);
                    crate::leanh::lean_ctor_set(v___x_4492_, 0, v___x_4500_);
                    v___x_4502_ = v___x_4492_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4514_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4500_);
                    v___x_4502_ = v_reuseFailAlloc_4514_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4503_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4503_, 0, v___x_4502_);
                crate::leanh::lean_ctor_set(v___x_4503_, 1, v_a_4486_);
                v___x_4504_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_4505_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4505_, 0, v___x_4503_);
                crate::leanh::lean_ctor_set(v___x_4505_, 1, v___x_4504_);
                v___x_4506_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4506_, 0, v___x_4505_);
                crate::leanh::lean_ctor_set(v___x_4506_, 1, v_a_4490_);
                v___x_4507_ = l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1;
                v___x_4508_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4508_, 0, v___x_4506_);
                crate::leanh::lean_ctor_set(v___x_4508_, 1, v___x_4507_);
                v___x_4509_ = l_Std_Format_indentD(v_a_4495_);
                v___x_4510_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4510_, 0, v___x_4508_);
                crate::leanh::lean_ctor_set(v___x_4510_, 1, v___x_4509_);
                if v_isShared_4498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4497_, 0, v___x_4510_);
                    v___x_4512_ = v___x_4497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
                    v___x_4512_ = v_reuseFailAlloc_4513_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4512_;
            }
            5 => {
                if v_isShared_4520_ == 0 {
                    v___x_4522_ = v___x_4519_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4523_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
                    v___x_4522_ = v_reuseFailAlloc_4523_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(
    mut v_pu_4525_: *mut crate::leanh::LeanObject,
    mut v_funDecl_4526_: *mut crate::leanh::LeanObject,
    mut v_a_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v_a_4529_: *mut crate::leanh::LeanObject,
    mut v_a_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
    mut v_a_4532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4533_: u8 = 0;
    let mut v_res_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4533_ = (crate::leanh::lean_unbox(v_pu_4525_) as u8);
    v_res_4534_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(
        v_pu_boxed_4533_,
        v_funDecl_4526_,
        v_a_4527_,
        v_a_4528_,
        v_a_4529_,
        v_a_4530_,
        v_a_4531_,
    );
    crate::leanh::lean_dec(v_a_4531_);
    crate::leanh::lean_dec_ref(v_a_4530_);
    crate::leanh::lean_dec(v_a_4529_);
    crate::leanh::lean_dec_ref(v_a_4528_);
    crate::leanh::lean_dec_ref(v_a_4527_);
    return v_res_4534_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppCode___boxed(
    mut v_pu_4535_: *mut crate::leanh::LeanObject,
    mut v_c_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
    mut v_a_4542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4543_: u8 = 0;
    let mut v_res_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4543_ = (crate::leanh::lean_unbox(v_pu_4535_) as u8);
    v_res_4544_ = l_Lean_Compiler_LCNF_PP_ppCode(
        v_pu_boxed_4543_,
        v_c_4536_,
        v_a_4537_,
        v_a_4538_,
        v_a_4539_,
        v_a_4540_,
        v_a_4541_,
    );
    crate::leanh::lean_dec(v_a_4541_);
    crate::leanh::lean_dec_ref(v_a_4540_);
    crate::leanh::lean_dec(v_a_4539_);
    crate::leanh::lean_dec_ref(v_a_4538_);
    crate::leanh::lean_dec_ref(v_a_4537_);
    return v_res_4544_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppDeclValue(
    mut v_pu_4548_: u8,
    mut v_b_4549_: *mut crate::leanh::LeanObject,
    mut v_a_4550_: *mut crate::leanh::LeanObject,
    mut v_a_4551_: *mut crate::leanh::LeanObject,
    mut v_a_4552_: *mut crate::leanh::LeanObject,
    mut v_a_4553_: *mut crate::leanh::LeanObject,
    mut v_a_4554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4560_: u8 = 0;
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4565_: u8 = 0;
    let mut v_unused_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_b_4549_) == 0 {
                    v_code_4556_ = crate::leanh::lean_ctor_get(v_b_4549_, 0);
                    crate::leanh::lean_inc_ref(v_code_4556_);
                    crate::leanh::lean_dec_ref_known(v_b_4549_, 1);
                    v___x_4557_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_4548_,
                        v_code_4556_,
                        v_a_4550_,
                        v_a_4551_,
                        v_a_4552_,
                        v_a_4553_,
                        v_a_4554_,
                    );
                    return v___x_4557_;
                } else {
                    v_isSharedCheck_4565_ = (!crate::leanh::lean_is_exclusive(v_b_4549_)) as u8;
                    if v_isSharedCheck_4565_ == 0 {
                        v_unused_4566_ = crate::leanh::lean_ctor_get(v_b_4549_, 0);
                        crate::leanh::lean_dec(v_unused_4566_);
                        v___x_4559_ = v_b_4549_;
                        v_isShared_4560_ = v_isSharedCheck_4565_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_4549_);
                        v___x_4559_ = crate::leanh::lean_box(0);
                        v_isShared_4560_ = v_isSharedCheck_4565_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4561_ = l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1;
                if v_isShared_4560_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4559_, 0);
                    crate::leanh::lean_ctor_set(v___x_4559_, 0, v___x_4561_);
                    v___x_4563_ = v___x_4559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
                    v___x_4563_ = v_reuseFailAlloc_4564_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(
    mut v_pu_4567_: *mut crate::leanh::LeanObject,
    mut v_b_4568_: *mut crate::leanh::LeanObject,
    mut v_a_4569_: *mut crate::leanh::LeanObject,
    mut v_a_4570_: *mut crate::leanh::LeanObject,
    mut v_a_4571_: *mut crate::leanh::LeanObject,
    mut v_a_4572_: *mut crate::leanh::LeanObject,
    mut v_a_4573_: *mut crate::leanh::LeanObject,
    mut v_a_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4575_: u8 = 0;
    let mut v_res_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4575_ = (crate::leanh::lean_unbox(v_pu_4567_) as u8);
    v_res_4576_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(
        v_pu_boxed_4575_,
        v_b_4568_,
        v_a_4569_,
        v_a_4570_,
        v_a_4571_,
        v_a_4572_,
        v_a_4573_,
    );
    crate::leanh::lean_dec(v_a_4573_);
    crate::leanh::lean_dec_ref(v_a_4572_);
    crate::leanh::lean_dec(v_a_4571_);
    crate::leanh::lean_dec_ref(v_a_4570_);
    crate::leanh::lean_dec_ref(v_a_4569_);
    return v_res_4576_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(
    mut v_opts_4577_: *mut crate::leanh::LeanObject,
    mut v_opt_4578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4579_ = crate::leanh::lean_ctor_get(v_opt_4578_, 0);
    v_defValue_4580_ = crate::leanh::lean_ctor_get(v_opt_4578_, 1);
    v_map_4581_ = crate::leanh::lean_ctor_get(v_opts_4577_, 0);
    v___x_4582_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4581_,
            v_name_4579_,
        );
    if crate::leanh::lean_obj_tag(v___x_4582_) == 0 {
        crate::leanh::lean_inc(v_defValue_4580_);
        return v_defValue_4580_;
    } else {
        let mut v_val_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4583_ = crate::leanh::lean_ctor_get(v___x_4582_, 0);
        crate::leanh::lean_inc(v_val_4583_);
        crate::leanh::lean_dec_ref_known(v___x_4582_, 1);
        if crate::leanh::lean_obj_tag(v_val_4583_) == 3 {
            let mut v_v_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_4584_ = crate::leanh::lean_ctor_get(v_val_4583_, 0);
            crate::leanh::lean_inc(v_v_4584_);
            crate::leanh::lean_dec_ref_known(v_val_4583_, 1);
            return v_v_4584_;
        } else {
            crate::leanh::lean_dec(v_val_4583_);
            crate::leanh::lean_inc(v_defValue_4580_);
            return v_defValue_4580_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(
    mut v_opts_4585_: *mut crate::leanh::LeanObject,
    mut v_opt_4586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4587_ =
        l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_opts_4585_, v_opt_4586_);
    crate::leanh::lean_dec_ref(v_opt_4586_);
    crate::leanh::lean_dec_ref(v_opts_4585_);
    return v_res_4587_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(
    mut v_o_4591_: *mut crate::leanh::LeanObject,
    mut v_k_4592_: *mut crate::leanh::LeanObject,
    mut v_v_4593_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4595_: u8 = 0;
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4598_: u8 = 0;
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: u8 = 0;
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_4594_ = crate::leanh::lean_ctor_get(v_o_4591_, 0);
                v_hasTrace_4595_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_4591_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4609_ = (!crate::leanh::lean_is_exclusive(v_o_4591_)) as u8;
                if v_isSharedCheck_4609_ == 0 {
                    v___x_4597_ = v_o_4591_;
                    v_isShared_4598_ = v_isSharedCheck_4609_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_4594_);
                    crate::leanh::lean_dec(v_o_4591_);
                    v___x_4597_ = crate::leanh::lean_box(0);
                    v_isShared_4598_ = v_isSharedCheck_4609_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4599_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_4599_, 0 as u32, v_v_4593_);
                crate::leanh::lean_inc(v_k_4592_);
                v___x_4600_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4592_, v___x_4599_, v_map_4594_);
                if v_hasTrace_4595_ == 0 {
                    v___x_4601_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1;
                    v___x_4602_ = l_Lean_Name_isPrefixOf(v___x_4601_, v_k_4592_);
                    crate::leanh::lean_dec(v_k_4592_);
                    if v_isShared_4598_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4597_, 0, v___x_4600_);
                        v___x_4604_ = v___x_4597_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4605_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4600_);
                        v___x_4604_ = v_reuseFailAlloc_4605_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4592_);
                    if v_isShared_4598_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4597_, 0, v___x_4600_);
                        v___x_4607_ = v___x_4597_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4608_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4600_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4608_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_4595_,
                        );
                        v___x_4607_ = v_reuseFailAlloc_4608_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4604_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4602_,
                );
                return v___x_4604_;
            }
            3 => {
                return v___x_4607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___boxed(
    mut v_o_4610_: *mut crate::leanh::LeanObject,
    mut v_k_4611_: *mut crate::leanh::LeanObject,
    mut v_v_4612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_4613_: u8 = 0;
    let mut v_res_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_4613_ = (crate::leanh::lean_unbox(v_v_4612_) as u8);
    v_res_4614_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(v_o_4610_, v_k_4611_, v_v_boxed_4613_);
    return v_res_4614_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(
    mut v_opts_4615_: *mut crate::leanh::LeanObject,
    mut v_opt_4616_: *mut crate::leanh::LeanObject,
    mut v_val_4617_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4618_ = crate::leanh::lean_ctor_get(v_opt_4616_, 0);
    crate::leanh::lean_inc(v_name_4618_);
    crate::leanh::lean_dec_ref(v_opt_4616_);
    v___x_4619_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(v_opts_4615_, v_name_4618_, v_val_4617_);
    return v___x_4619_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(
    mut v_opts_4620_: *mut crate::leanh::LeanObject,
    mut v_opt_4621_: *mut crate::leanh::LeanObject,
    mut v_val_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_4623_: u8 = 0;
    let mut v_res_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_4623_ = (crate::leanh::lean_unbox(v_val_4622_) as u8);
    v_res_4624_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(
        v_opts_4620_,
        v_opt_4621_,
        v_val_boxed_4623_,
    );
    return v_res_4624_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4625_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4626_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once),
        _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0,
    );
    v___x_4627_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4627_, 0, v___x_4626_);
    return v___x_4627_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4628_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once),
        _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1,
    );
    v___x_4629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4629_, 0, v___x_4628_);
    crate::leanh::lean_ctor_set(v___x_4629_, 1, v___x_4628_);
    return v___x_4629_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_run___redArg(
    mut v_x_4630_: *mut crate::leanh::LeanObject,
    mut v_a_4631_: *mut crate::leanh::LeanObject,
    mut v_a_4632_: *mut crate::leanh::LeanObject,
    mut v_a_4633_: *mut crate::leanh::LeanObject,
    mut v_a_4634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: u8 = 0;
    let mut v___y_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4659_: u8 = 0;
    let mut v_inheritedTraceOptions_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: u8 = 0;
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4673_: u8 = 0;
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4677_: u8 = 0;
    let mut v___y_4679_: u8 = 0;
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut v_unused_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4636_ = lean_st_ref_get(v_a_4634_);
                v_options_4637_ = crate::leanh::lean_ctor_get(v_a_4633_, 2);
                v_env_4638_ = crate::leanh::lean_ctor_get(v___x_4636_, 0);
                crate::leanh::lean_inc_ref(v_env_4638_);
                crate::leanh::lean_dec(v___x_4636_);
                v___x_4639_ = l_Lean_pp_sanitizeNames;
                v___x_4640_ = 0;
                crate::leanh::lean_inc_ref(v_options_4637_);
                v___x_4641_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(
                    v_options_4637_,
                    v___x_4639_,
                    v___x_4640_,
                );
                v___x_4642_ = l_Lean_diagnostics;
                v___x_4643_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                    v___x_4641_,
                    v___x_4642_,
                );
                v___x_4700_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4638_);
                crate::leanh::lean_dec_ref(v_env_4638_);
                if v___x_4700_ == 0 {
                    if v___x_4643_ == 0 {
                        v___y_4645_ = v_a_4633_;
                        v___y_4646_ = v_a_4634_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4679_ = v___x_4700_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_4679_ = v___x_4643_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_4647_ = lean_st_ref_get(v_a_4632_);
                v_fileName_4648_ = crate::leanh::lean_ctor_get(v___y_4645_, 0);
                v_fileMap_4649_ = crate::leanh::lean_ctor_get(v___y_4645_, 1);
                v_currRecDepth_4650_ = crate::leanh::lean_ctor_get(v___y_4645_, 3);
                v_ref_4651_ = crate::leanh::lean_ctor_get(v___y_4645_, 5);
                v_currNamespace_4652_ = crate::leanh::lean_ctor_get(v___y_4645_, 6);
                v_openDecls_4653_ = crate::leanh::lean_ctor_get(v___y_4645_, 7);
                v_initHeartbeats_4654_ = crate::leanh::lean_ctor_get(v___y_4645_, 8);
                v_maxHeartbeats_4655_ = crate::leanh::lean_ctor_get(v___y_4645_, 9);
                v_quotContext_4656_ = crate::leanh::lean_ctor_get(v___y_4645_, 10);
                v_currMacroScope_4657_ = crate::leanh::lean_ctor_get(v___y_4645_, 11);
                v_cancelTk_x3f_4658_ = crate::leanh::lean_ctor_get(v___y_4645_, 12);
                v_suppressElabErrors_4659_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4660_ = crate::leanh::lean_ctor_get(v___y_4645_, 13);
                v___x_4661_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_4631_);
                if crate::leanh::lean_obj_tag(v___x_4661_) == 0 {
                    v_a_4662_ = crate::leanh::lean_ctor_get(v___x_4661_, 0);
                    crate::leanh::lean_inc(v_a_4662_);
                    crate::leanh::lean_dec_ref_known(v___x_4661_, 1);
                    v_lctx_4663_ = crate::leanh::lean_ctor_get(v___x_4647_, 0);
                    crate::leanh::lean_inc_ref(v_lctx_4663_);
                    crate::leanh::lean_dec(v___x_4647_);
                    v___x_4664_ = l_Lean_maxRecDepth;
                    v___x_4665_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(
                        v___x_4641_,
                        v___x_4664_,
                    );
                    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4660_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_4658_);
                    crate::leanh::lean_inc(v_currMacroScope_4657_);
                    crate::leanh::lean_inc(v_quotContext_4656_);
                    crate::leanh::lean_inc(v_maxHeartbeats_4655_);
                    crate::leanh::lean_inc(v_initHeartbeats_4654_);
                    crate::leanh::lean_inc(v_openDecls_4653_);
                    crate::leanh::lean_inc(v_currNamespace_4652_);
                    crate::leanh::lean_inc(v_ref_4651_);
                    crate::leanh::lean_inc(v_currRecDepth_4650_);
                    crate::leanh::lean_inc_ref(v_fileMap_4649_);
                    crate::leanh::lean_inc_ref(v_fileName_4648_);
                    v___x_4666_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_4666_, 0, v_fileName_4648_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 1, v_fileMap_4649_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 2, v___x_4641_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 3, v_currRecDepth_4650_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 4, v___x_4665_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 5, v_ref_4651_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 6, v_currNamespace_4652_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 7, v_openDecls_4653_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 8, v_initHeartbeats_4654_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 9, v_maxHeartbeats_4655_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 10, v_quotContext_4656_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 11, v_currMacroScope_4657_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 12, v_cancelTk_x3f_4658_);
                    crate::leanh::lean_ctor_set(v___x_4666_, 13, v_inheritedTraceOptions_4660_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4666_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        v___x_4643_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4666_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_4659_,
                    );
                    v___x_4667_ = (crate::leanh::lean_unbox(v_a_4662_) as u8);
                    crate::leanh::lean_dec(v_a_4662_);
                    v___x_4668_ =
                        l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4663_, v___x_4667_);
                    crate::leanh::lean_dec_ref(v_lctx_4663_);
                    crate::leanh::lean_inc(v___y_4646_);
                    crate::leanh::lean_inc(v_a_4632_);
                    crate::leanh::lean_inc_ref(v_a_4631_);
                    v___x_4669_ = crate::leanh::lean_apply_6(
                        v_x_4630_,
                        v___x_4668_,
                        v_a_4631_,
                        v_a_4632_,
                        v___x_4666_,
                        v___y_4646_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4669_;
                } else {
                    crate::leanh::lean_dec(v___x_4647_);
                    crate::leanh::lean_dec_ref(v___x_4641_);
                    crate::leanh::lean_dec_ref(v_x_4630_);
                    v_a_4670_ = crate::leanh::lean_ctor_get(v___x_4661_, 0);
                    v_isSharedCheck_4677_ = (!crate::leanh::lean_is_exclusive(v___x_4661_)) as u8;
                    if v_isSharedCheck_4677_ == 0 {
                        v___x_4672_ = v___x_4661_;
                        v_isShared_4673_ = v_isSharedCheck_4677_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4670_);
                        crate::leanh::lean_dec(v___x_4661_);
                        v___x_4672_ = crate::leanh::lean_box(0);
                        v_isShared_4673_ = v_isSharedCheck_4677_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4673_ == 0 {
                    v___x_4675_ = v___x_4672_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4676_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
                    v___x_4675_ = v_reuseFailAlloc_4676_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4675_;
            }
            4 => {
                if v___y_4679_ == 0 {
                    v___x_4680_ = lean_st_ref_take(v_a_4634_);
                    v_env_4681_ = crate::leanh::lean_ctor_get(v___x_4680_, 0);
                    v_nextMacroScope_4682_ = crate::leanh::lean_ctor_get(v___x_4680_, 1);
                    v_ngen_4683_ = crate::leanh::lean_ctor_get(v___x_4680_, 2);
                    v_auxDeclNGen_4684_ = crate::leanh::lean_ctor_get(v___x_4680_, 3);
                    v_traceState_4685_ = crate::leanh::lean_ctor_get(v___x_4680_, 4);
                    v_messages_4686_ = crate::leanh::lean_ctor_get(v___x_4680_, 6);
                    v_infoState_4687_ = crate::leanh::lean_ctor_get(v___x_4680_, 7);
                    v_snapshotTasks_4688_ = crate::leanh::lean_ctor_get(v___x_4680_, 8);
                    v_isSharedCheck_4698_ = (!crate::leanh::lean_is_exclusive(v___x_4680_)) as u8;
                    if v_isSharedCheck_4698_ == 0 {
                        v_unused_4699_ = crate::leanh::lean_ctor_get(v___x_4680_, 5);
                        crate::leanh::lean_dec(v_unused_4699_);
                        v___x_4690_ = v___x_4680_;
                        v_isShared_4691_ = v_isSharedCheck_4698_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_4688_);
                        crate::leanh::lean_inc(v_infoState_4687_);
                        crate::leanh::lean_inc(v_messages_4686_);
                        crate::leanh::lean_inc(v_traceState_4685_);
                        crate::leanh::lean_inc(v_auxDeclNGen_4684_);
                        crate::leanh::lean_inc(v_ngen_4683_);
                        crate::leanh::lean_inc(v_nextMacroScope_4682_);
                        crate::leanh::lean_inc(v_env_4681_);
                        crate::leanh::lean_dec(v___x_4680_);
                        v___x_4690_ = crate::leanh::lean_box(0);
                        v_isShared_4691_ = v_isSharedCheck_4698_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_4645_ = v_a_4633_;
                    v___y_4646_ = v_a_4634_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_4692_ = l_Lean_Kernel_enableDiag(v_env_4681_, v___x_4643_);
                v___x_4693_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__2_once),
                    _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2,
                );
                if v_isShared_4691_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4690_, 5, v___x_4693_);
                    crate::leanh::lean_ctor_set(v___x_4690_, 0, v___x_4692_);
                    v___x_4695_ = v___x_4690_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4697_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_nextMacroScope_4682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_ngen_4683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 3, v_auxDeclNGen_4684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 4, v_traceState_4685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 5, v___x_4693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 6, v_messages_4686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 7, v_infoState_4687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 8, v_snapshotTasks_4688_);
                    v___x_4695_ = v_reuseFailAlloc_4697_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4696_ = lean_st_ref_set(v_a_4634_, v___x_4695_);
                v___y_4645_ = v_a_4633_;
                v___y_4646_ = v_a_4634_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_run___redArg___boxed(
    mut v_x_4701_: *mut crate::leanh::LeanObject,
    mut v_a_4702_: *mut crate::leanh::LeanObject,
    mut v_a_4703_: *mut crate::leanh::LeanObject,
    mut v_a_4704_: *mut crate::leanh::LeanObject,
    mut v_a_4705_: *mut crate::leanh::LeanObject,
    mut v_a_4706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4707_ =
        l_Lean_Compiler_LCNF_PP_run___redArg(v_x_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
    crate::leanh::lean_dec(v_a_4705_);
    crate::leanh::lean_dec_ref(v_a_4704_);
    crate::leanh::lean_dec(v_a_4703_);
    crate::leanh::lean_dec_ref(v_a_4702_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_run(
    mut v_00_u03b1_4708_: *mut crate::leanh::LeanObject,
    mut v_x_4709_: *mut crate::leanh::LeanObject,
    mut v_a_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4715_ =
        l_Lean_Compiler_LCNF_PP_run___redArg(v_x_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_);
    return v___x_4715_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_run___boxed(
    mut v_00_u03b1_4716_: *mut crate::leanh::LeanObject,
    mut v_x_4717_: *mut crate::leanh::LeanObject,
    mut v_a_4718_: *mut crate::leanh::LeanObject,
    mut v_a_4719_: *mut crate::leanh::LeanObject,
    mut v_a_4720_: *mut crate::leanh::LeanObject,
    mut v_a_4721_: *mut crate::leanh::LeanObject,
    mut v_a_4722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4723_ = l_Lean_Compiler_LCNF_PP_run(
        v_00_u03b1_4716_,
        v_x_4717_,
        v_a_4718_,
        v_a_4719_,
        v_a_4720_,
        v_a_4721_,
    );
    crate::leanh::lean_dec(v_a_4721_);
    crate::leanh::lean_dec_ref(v_a_4720_);
    crate::leanh::lean_dec(v_a_4719_);
    crate::leanh::lean_dec_ref(v_a_4718_);
    return v_res_4723_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode(
    mut v_pu_4724_: u8,
    mut v_code_4725_: *mut crate::leanh::LeanObject,
    mut v_a_4726_: *mut crate::leanh::LeanObject,
    mut v_a_4727_: *mut crate::leanh::LeanObject,
    mut v_a_4728_: *mut crate::leanh::LeanObject,
    mut v_a_4729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4731_ = crate::leanh::lean_box((v_pu_4724_) as usize);
    v___x_4732_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PP_ppCode___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4732_, 0, v___x_4731_);
    crate::leanh::lean_closure_set(v___x_4732_, 1, v_code_4725_);
    v___x_4733_ = l_Lean_Compiler_LCNF_PP_run___redArg(
        v___x_4732_,
        v_a_4726_,
        v_a_4727_,
        v_a_4728_,
        v_a_4729_,
    );
    return v___x_4733_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode___boxed(
    mut v_pu_4734_: *mut crate::leanh::LeanObject,
    mut v_code_4735_: *mut crate::leanh::LeanObject,
    mut v_a_4736_: *mut crate::leanh::LeanObject,
    mut v_a_4737_: *mut crate::leanh::LeanObject,
    mut v_a_4738_: *mut crate::leanh::LeanObject,
    mut v_a_4739_: *mut crate::leanh::LeanObject,
    mut v_a_4740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4741_: u8 = 0;
    let mut v_res_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4741_ = (crate::leanh::lean_unbox(v_pu_4734_) as u8);
    v_res_4742_ = l_Lean_Compiler_LCNF_ppCode(
        v_pu_boxed_4741_,
        v_code_4735_,
        v_a_4736_,
        v_a_4737_,
        v_a_4738_,
        v_a_4739_,
    );
    crate::leanh::lean_dec(v_a_4739_);
    crate::leanh::lean_dec_ref(v_a_4738_);
    crate::leanh::lean_dec(v_a_4737_);
    crate::leanh::lean_dec_ref(v_a_4736_);
    return v_res_4742_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppLetValue(
    mut v_pu_4743_: u8,
    mut v_e_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_a_4746_: *mut crate::leanh::LeanObject,
    mut v_a_4747_: *mut crate::leanh::LeanObject,
    mut v_a_4748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4750_ = crate::leanh::lean_box((v_pu_4743_) as usize);
    v___x_4751_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PP_ppLetValue___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4751_, 0, v___x_4750_);
    crate::leanh::lean_closure_set(v___x_4751_, 1, v_e_4744_);
    v___x_4752_ = l_Lean_Compiler_LCNF_PP_run___redArg(
        v___x_4751_,
        v_a_4745_,
        v_a_4746_,
        v_a_4747_,
        v_a_4748_,
    );
    return v___x_4752_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppLetValue___boxed(
    mut v_pu_4753_: *mut crate::leanh::LeanObject,
    mut v_e_4754_: *mut crate::leanh::LeanObject,
    mut v_a_4755_: *mut crate::leanh::LeanObject,
    mut v_a_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
    mut v_a_4759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4760_: u8 = 0;
    let mut v_res_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4760_ = (crate::leanh::lean_unbox(v_pu_4753_) as u8);
    v_res_4761_ = l_Lean_Compiler_LCNF_ppLetValue(
        v_pu_boxed_4760_,
        v_e_4754_,
        v_a_4755_,
        v_a_4756_,
        v_a_4757_,
        v_a_4758_,
    );
    crate::leanh::lean_dec(v_a_4758_);
    crate::leanh::lean_dec_ref(v_a_4757_);
    crate::leanh::lean_dec(v_a_4756_);
    crate::leanh::lean_dec_ref(v_a_4755_);
    return v_res_4761_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl___lam__0(
    mut v_pu_4765_: u8,
    mut v_params_4766_: *mut crate::leanh::LeanObject,
    mut v_type_4767_: *mut crate::leanh::LeanObject,
    mut v_value_4768_: *mut crate::leanh::LeanObject,
    mut v_name_4769_: *mut crate::leanh::LeanObject,
    mut v___y_4770_: *mut crate::leanh::LeanObject,
    mut v___y_4771_: *mut crate::leanh::LeanObject,
    mut v___y_4772_: *mut crate::leanh::LeanObject,
    mut v___y_4773_: *mut crate::leanh::LeanObject,
    mut v___y_4774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4784_: u8 = 0;
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4789_: u8 = 0;
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut v_a_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4776_ = l_Lean_Compiler_LCNF_PP_ppParams(
                    v_pu_4765_,
                    v_params_4766_,
                    v___y_4770_,
                    v___y_4771_,
                    v___y_4772_,
                    v___y_4773_,
                    v___y_4774_,
                );
                if crate::leanh::lean_obj_tag(v___x_4776_) == 0 {
                    v_a_4777_ = crate::leanh::lean_ctor_get(v___x_4776_, 0);
                    crate::leanh::lean_inc(v_a_4777_);
                    crate::leanh::lean_dec_ref_known(v___x_4776_, 1);
                    v___x_4778_ = l_Lean_Compiler_LCNF_PP_getFunType(
                        v_pu_4765_,
                        v_params_4766_,
                        v_type_4767_,
                        v___y_4773_,
                        v___y_4774_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4778_) == 0 {
                        v_a_4779_ = crate::leanh::lean_ctor_get(v___x_4778_, 0);
                        crate::leanh::lean_inc(v_a_4779_);
                        crate::leanh::lean_dec_ref_known(v___x_4778_, 1);
                        v___x_4780_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                            v_a_4779_,
                            v___y_4770_,
                            v___y_4773_,
                            v___y_4774_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4780_) == 0 {
                            v_a_4781_ = crate::leanh::lean_ctor_get(v___x_4780_, 0);
                            v_isSharedCheck_4809_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4780_)) as u8;
                            if v_isSharedCheck_4809_ == 0 {
                                v___x_4783_ = v___x_4780_;
                                v_isShared_4784_ = v_isSharedCheck_4809_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4781_);
                                crate::leanh::lean_dec(v___x_4780_);
                                v___x_4783_ = crate::leanh::lean_box(0);
                                v_isShared_4784_ = v_isSharedCheck_4809_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4777_);
                            crate::leanh::lean_dec(v_name_4769_);
                            crate::leanh::lean_dec_ref(v_value_4768_);
                            return v___x_4780_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4777_);
                        crate::leanh::lean_dec(v_name_4769_);
                        crate::leanh::lean_dec_ref(v_value_4768_);
                        v_a_4810_ = crate::leanh::lean_ctor_get(v___x_4778_, 0);
                        v_isSharedCheck_4817_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4778_)) as u8;
                        if v_isSharedCheck_4817_ == 0 {
                            v___x_4812_ = v___x_4778_;
                            v_isShared_4813_ = v_isSharedCheck_4817_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4810_);
                            crate::leanh::lean_dec(v___x_4778_);
                            v___x_4812_ = crate::leanh::lean_box(0);
                            v_isShared_4813_ = v_isSharedCheck_4817_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_name_4769_);
                    crate::leanh::lean_dec_ref(v_value_4768_);
                    crate::leanh::lean_dec_ref(v_type_4767_);
                    crate::leanh::lean_dec_ref(v_params_4766_);
                    return v___x_4776_;
                }
            }
            1 => {
                v___x_4785_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(
                    v_pu_4765_,
                    v_value_4768_,
                    v___y_4770_,
                    v___y_4771_,
                    v___y_4772_,
                    v___y_4773_,
                    v___y_4774_,
                );
                if crate::leanh::lean_obj_tag(v___x_4785_) == 0 {
                    v_a_4786_ = crate::leanh::lean_ctor_get(v___x_4785_, 0);
                    v_isSharedCheck_4808_ = (!crate::leanh::lean_is_exclusive(v___x_4785_)) as u8;
                    if v_isSharedCheck_4808_ == 0 {
                        v___x_4788_ = v___x_4785_;
                        v_isShared_4789_ = v_isSharedCheck_4808_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4786_);
                        crate::leanh::lean_dec(v___x_4785_);
                        v___x_4788_ = crate::leanh::lean_box(0);
                        v_isShared_4789_ = v_isSharedCheck_4808_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4783_);
                    crate::leanh::lean_dec(v_a_4781_);
                    crate::leanh::lean_dec(v_a_4777_);
                    crate::leanh::lean_dec(v_name_4769_);
                    return v___x_4785_;
                }
            }
            2 => {
                v___x_4790_ = l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1;
                v___x_4791_ = 1;
                v___x_4792_ = l_Lean_Name_toString(v_name_4769_, v___x_4791_);
                if v_isShared_4784_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4783_, 3);
                    crate::leanh::lean_ctor_set(v___x_4783_, 0, v___x_4792_);
                    v___x_4794_ = v___x_4783_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4807_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4792_);
                    v___x_4794_ = v_reuseFailAlloc_4807_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4795_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4795_, 0, v___x_4790_);
                crate::leanh::lean_ctor_set(v___x_4795_, 1, v___x_4794_);
                v___x_4796_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4796_, 0, v___x_4795_);
                crate::leanh::lean_ctor_set(v___x_4796_, 1, v_a_4777_);
                v___x_4797_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_4798_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4798_, 0, v___x_4796_);
                crate::leanh::lean_ctor_set(v___x_4798_, 1, v___x_4797_);
                v___x_4799_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4799_, 0, v___x_4798_);
                crate::leanh::lean_ctor_set(v___x_4799_, 1, v_a_4781_);
                v___x_4800_ = l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1;
                v___x_4801_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4801_, 0, v___x_4799_);
                crate::leanh::lean_ctor_set(v___x_4801_, 1, v___x_4800_);
                v___x_4802_ = l_Std_Format_indentD(v_a_4786_);
                v___x_4803_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4803_, 0, v___x_4801_);
                crate::leanh::lean_ctor_set(v___x_4803_, 1, v___x_4802_);
                if v_isShared_4789_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4788_, 0, v___x_4803_);
                    v___x_4805_ = v___x_4788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4803_);
                    v___x_4805_ = v_reuseFailAlloc_4806_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4805_;
            }
            5 => {
                if v_isShared_4813_ == 0 {
                    v___x_4815_ = v___x_4812_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
                    v___x_4815_ = v_reuseFailAlloc_4816_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(
    mut v_pu_4818_: *mut crate::leanh::LeanObject,
    mut v_params_4819_: *mut crate::leanh::LeanObject,
    mut v_type_4820_: *mut crate::leanh::LeanObject,
    mut v_value_4821_: *mut crate::leanh::LeanObject,
    mut v_name_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
    mut v___y_4828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4829_: u8 = 0;
    let mut v_res_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4829_ = (crate::leanh::lean_unbox(v_pu_4818_) as u8);
    v_res_4830_ = l_Lean_Compiler_LCNF_ppDecl___lam__0(
        v_pu_boxed_4829_,
        v_params_4819_,
        v_type_4820_,
        v_value_4821_,
        v_name_4822_,
        v___y_4823_,
        v___y_4824_,
        v___y_4825_,
        v___y_4826_,
        v___y_4827_,
    );
    crate::leanh::lean_dec(v___y_4827_);
    crate::leanh::lean_dec_ref(v___y_4826_);
    crate::leanh::lean_dec(v___y_4825_);
    crate::leanh::lean_dec_ref(v___y_4824_);
    crate::leanh::lean_dec_ref(v___y_4823_);
    return v_res_4830_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl(
    mut v_pu_4831_: u8,
    mut v_decl_4832_: *mut crate::leanh::LeanObject,
    mut v_a_4833_: *mut crate::leanh::LeanObject,
    mut v_a_4834_: *mut crate::leanh::LeanObject,
    mut v_a_4835_: *mut crate::leanh::LeanObject,
    mut v_a_4836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toSignature_4838_ = crate::leanh::lean_ctor_get(v_decl_4832_, 0);
    crate::leanh::lean_inc_ref(v_toSignature_4838_);
    v_value_4839_ = crate::leanh::lean_ctor_get(v_decl_4832_, 1);
    crate::leanh::lean_inc_ref(v_value_4839_);
    crate::leanh::lean_dec_ref(v_decl_4832_);
    v_name_4840_ = crate::leanh::lean_ctor_get(v_toSignature_4838_, 0);
    crate::leanh::lean_inc(v_name_4840_);
    v_type_4841_ = crate::leanh::lean_ctor_get(v_toSignature_4838_, 2);
    crate::leanh::lean_inc_ref(v_type_4841_);
    v_params_4842_ = crate::leanh::lean_ctor_get(v_toSignature_4838_, 3);
    crate::leanh::lean_inc_ref(v_params_4842_);
    crate::leanh::lean_dec_ref(v_toSignature_4838_);
    v___x_4843_ = crate::leanh::lean_box((v_pu_4831_) as usize);
    v___f_4844_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed as *mut core::ffi::c_void,
        11,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4844_, 0, v___x_4843_);
    crate::leanh::lean_closure_set(v___f_4844_, 1, v_params_4842_);
    crate::leanh::lean_closure_set(v___f_4844_, 2, v_type_4841_);
    crate::leanh::lean_closure_set(v___f_4844_, 3, v_value_4839_);
    crate::leanh::lean_closure_set(v___f_4844_, 4, v_name_4840_);
    v___x_4845_ = l_Lean_Compiler_LCNF_PP_run___redArg(
        v___f_4844_,
        v_a_4833_,
        v_a_4834_,
        v_a_4835_,
        v_a_4836_,
    );
    return v___x_4845_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl___boxed(
    mut v_pu_4846_: *mut crate::leanh::LeanObject,
    mut v_decl_4847_: *mut crate::leanh::LeanObject,
    mut v_a_4848_: *mut crate::leanh::LeanObject,
    mut v_a_4849_: *mut crate::leanh::LeanObject,
    mut v_a_4850_: *mut crate::leanh::LeanObject,
    mut v_a_4851_: *mut crate::leanh::LeanObject,
    mut v_a_4852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4853_: u8 = 0;
    let mut v_res_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4853_ = (crate::leanh::lean_unbox(v_pu_4846_) as u8);
    v_res_4854_ = l_Lean_Compiler_LCNF_ppDecl(
        v_pu_boxed_4853_,
        v_decl_4847_,
        v_a_4848_,
        v_a_4849_,
        v_a_4850_,
        v_a_4851_,
    );
    crate::leanh::lean_dec(v_a_4851_);
    crate::leanh::lean_dec_ref(v_a_4850_);
    crate::leanh::lean_dec(v_a_4849_);
    crate::leanh::lean_dec_ref(v_a_4848_);
    return v_res_4854_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppFunDecl___lam__0(
    mut v_pu_4855_: u8,
    mut v_decl_4856_: *mut crate::leanh::LeanObject,
    mut v___y_4857_: *mut crate::leanh::LeanObject,
    mut v___y_4858_: *mut crate::leanh::LeanObject,
    mut v___y_4859_: *mut crate::leanh::LeanObject,
    mut v___y_4860_: *mut crate::leanh::LeanObject,
    mut v___y_4861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4863_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(
                    v_pu_4855_,
                    v_decl_4856_,
                    v___y_4857_,
                    v___y_4858_,
                    v___y_4859_,
                    v___y_4860_,
                    v___y_4861_,
                );
                if crate::leanh::lean_obj_tag(v___x_4863_) == 0 {
                    v_a_4864_ = crate::leanh::lean_ctor_get(v___x_4863_, 0);
                    v_isSharedCheck_4873_ = (!crate::leanh::lean_is_exclusive(v___x_4863_)) as u8;
                    if v_isSharedCheck_4873_ == 0 {
                        v___x_4866_ = v___x_4863_;
                        v_isShared_4867_ = v_isSharedCheck_4873_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4864_);
                        crate::leanh::lean_dec(v___x_4863_);
                        v___x_4866_ = crate::leanh::lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4873_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4863_;
                }
            }
            1 => {
                v___x_4868_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__3;
                v___x_4869_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4869_, 0, v___x_4868_);
                crate::leanh::lean_ctor_set(v___x_4869_, 1, v_a_4864_);
                if v_isShared_4867_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4866_, 0, v___x_4869_);
                    v___x_4871_ = v___x_4866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4869_);
                    v___x_4871_ = v_reuseFailAlloc_4872_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(
    mut v_pu_4874_: *mut crate::leanh::LeanObject,
    mut v_decl_4875_: *mut crate::leanh::LeanObject,
    mut v___y_4876_: *mut crate::leanh::LeanObject,
    mut v___y_4877_: *mut crate::leanh::LeanObject,
    mut v___y_4878_: *mut crate::leanh::LeanObject,
    mut v___y_4879_: *mut crate::leanh::LeanObject,
    mut v___y_4880_: *mut crate::leanh::LeanObject,
    mut v___y_4881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4882_: u8 = 0;
    let mut v_res_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4882_ = (crate::leanh::lean_unbox(v_pu_4874_) as u8);
    v_res_4883_ = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(
        v_pu_boxed_4882_,
        v_decl_4875_,
        v___y_4876_,
        v___y_4877_,
        v___y_4878_,
        v___y_4879_,
        v___y_4880_,
    );
    crate::leanh::lean_dec(v___y_4880_);
    crate::leanh::lean_dec_ref(v___y_4879_);
    crate::leanh::lean_dec(v___y_4878_);
    crate::leanh::lean_dec_ref(v___y_4877_);
    crate::leanh::lean_dec_ref(v___y_4876_);
    return v_res_4883_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppFunDecl(
    mut v_pu_4884_: u8,
    mut v_decl_4885_: *mut crate::leanh::LeanObject,
    mut v_a_4886_: *mut crate::leanh::LeanObject,
    mut v_a_4887_: *mut crate::leanh::LeanObject,
    mut v_a_4888_: *mut crate::leanh::LeanObject,
    mut v_a_4889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4891_ = crate::leanh::lean_box((v_pu_4884_) as usize);
    v___f_4892_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4892_, 0, v___x_4891_);
    crate::leanh::lean_closure_set(v___f_4892_, 1, v_decl_4885_);
    v___x_4893_ = l_Lean_Compiler_LCNF_PP_run___redArg(
        v___f_4892_,
        v_a_4886_,
        v_a_4887_,
        v_a_4888_,
        v_a_4889_,
    );
    return v___x_4893_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppFunDecl___boxed(
    mut v_pu_4894_: *mut crate::leanh::LeanObject,
    mut v_decl_4895_: *mut crate::leanh::LeanObject,
    mut v_a_4896_: *mut crate::leanh::LeanObject,
    mut v_a_4897_: *mut crate::leanh::LeanObject,
    mut v_a_4898_: *mut crate::leanh::LeanObject,
    mut v_a_4899_: *mut crate::leanh::LeanObject,
    mut v_a_4900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4901_: u8 = 0;
    let mut v_res_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4901_ = (crate::leanh::lean_unbox(v_pu_4894_) as u8);
    v_res_4902_ = l_Lean_Compiler_LCNF_ppFunDecl(
        v_pu_boxed_4901_,
        v_decl_4895_,
        v_a_4896_,
        v_a_4897_,
        v_a_4898_,
        v_a_4899_,
    );
    crate::leanh::lean_dec(v_a_4899_);
    crate::leanh::lean_dec_ref(v_a_4898_);
    crate::leanh::lean_dec(v_a_4897_);
    crate::leanh::lean_dec_ref(v_a_4896_);
    return v_res_4902_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(
    mut v_a_4903_: *mut crate::leanh::LeanObject,
    mut v_val_4904_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4907_ = lean_st_ref_set(v_a_4903_, v_val_4904_);
    v___x_4908_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4908_, 0, v___x_4907_);
    return v___x_4908_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(
    mut v_a_4909_: *mut crate::leanh::LeanObject,
    mut v_val_4910_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4913_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(
        v_a_4909_,
        v_val_4910_,
        v_a_x3f_4911_,
    );
    crate::leanh::lean_dec(v_a_x3f_4911_);
    crate::leanh::lean_dec(v_a_4909_);
    return v_res_4913_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4914_ = crate::leanh::lean_box(0);
    v___x_4915_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4916_ = lean_mk_array(v___x_4915_, v___x_4914_);
    return v___x_4916_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4917_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0,
    );
    v___x_4918_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4919_, 0, v___x_4918_);
    crate::leanh::lean_ctor_set(v___x_4919_, 1, v___x_4917_);
    return v___x_4919_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1,
    );
    v___x_4921_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4921_, 0, v___x_4920_);
    crate::leanh::lean_ctor_set(v___x_4921_, 1, v___x_4920_);
    crate::leanh::lean_ctor_set(v___x_4921_, 2, v___x_4920_);
    crate::leanh::lean_ctor_set(v___x_4921_, 3, v___x_4920_);
    crate::leanh::lean_ctor_set(v___x_4921_, 4, v___x_4920_);
    crate::leanh::lean_ctor_set(v___x_4921_, 5, v___x_4920_);
    return v___x_4921_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4922_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4923_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2,
    );
    v___x_4924_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4924_, 0, v___x_4923_);
    crate::leanh::lean_ctor_set(v___x_4924_, 1, v___x_4922_);
    return v___x_4924_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
    mut v_phase_4925_: u8,
    mut v_x_4926_: *mut crate::leanh::LeanObject,
    mut v_a_4927_: *mut crate::leanh::LeanObject,
    mut v_a_4928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4946_: u8 = 0;
    let mut v_unused_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_a_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4955_: u8 = 0;
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4959_: u8 = 0;
    let mut v_unused_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4930_ = lean_st_ref_get(v_a_4928_);
                v___x_4931_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once), _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3);
                v_r_4932_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(
                    v_x_4926_,
                    v___x_4931_,
                    v_phase_4925_,
                    v_a_4927_,
                    v_a_4928_,
                );
                if crate::leanh::lean_obj_tag(v_r_4932_) == 0 {
                    v_a_4933_ = crate::leanh::lean_ctor_get(v_r_4932_, 0);
                    v_isSharedCheck_4949_ = (!crate::leanh::lean_is_exclusive(v_r_4932_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v___x_4935_ = v_r_4932_;
                        v_isShared_4936_ = v_isSharedCheck_4949_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4933_);
                        crate::leanh::lean_dec(v_r_4932_);
                        v___x_4935_ = crate::leanh::lean_box(0);
                        v_isShared_4936_ = v_isSharedCheck_4949_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4950_ = crate::leanh::lean_ctor_get(v_r_4932_, 0);
                    crate::leanh::lean_inc(v_a_4950_);
                    crate::leanh::lean_dec_ref_known(v_r_4932_, 1);
                    v___x_4951_ = crate::leanh::lean_box(0);
                    v___x_4952_ =
                        l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(
                            v_a_4928_,
                            v___x_4930_,
                            v___x_4951_,
                        );
                    v_isSharedCheck_4959_ = (!crate::leanh::lean_is_exclusive(v___x_4952_)) as u8;
                    if v_isSharedCheck_4959_ == 0 {
                        v_unused_4960_ = crate::leanh::lean_ctor_get(v___x_4952_, 0);
                        crate::leanh::lean_dec(v_unused_4960_);
                        v___x_4954_ = v___x_4952_;
                        v_isShared_4955_ = v_isSharedCheck_4959_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4952_);
                        v___x_4954_ = crate::leanh::lean_box(0);
                        v_isShared_4955_ = v_isSharedCheck_4959_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_4933_);
                if v_isShared_4936_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4935_, 1);
                    v___x_4938_ = v___x_4935_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4933_);
                    v___x_4938_ = v_reuseFailAlloc_4948_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4939_ =
                    l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(
                        v_a_4928_,
                        v___x_4930_,
                        v___x_4938_,
                    );
                crate::leanh::lean_dec_ref(v___x_4938_);
                v_isSharedCheck_4946_ = (!crate::leanh::lean_is_exclusive(v___x_4939_)) as u8;
                if v_isSharedCheck_4946_ == 0 {
                    v_unused_4947_ = crate::leanh::lean_ctor_get(v___x_4939_, 0);
                    crate::leanh::lean_dec(v_unused_4947_);
                    v___x_4941_ = v___x_4939_;
                    v_isShared_4942_ = v_isSharedCheck_4946_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4939_);
                    v___x_4941_ = crate::leanh::lean_box(0);
                    v_isShared_4942_ = v_isSharedCheck_4946_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4941_, 0, v_a_4933_);
                    v___x_4944_ = v___x_4941_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4945_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4933_);
                    v___x_4944_ = v_reuseFailAlloc_4945_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4944_;
            }
            5 => {
                if v_isShared_4955_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4954_, 1);
                    crate::leanh::lean_ctor_set(v___x_4954_, 0, v_a_4950_);
                    v___x_4957_ = v___x_4954_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4950_);
                    v___x_4957_ = v_reuseFailAlloc_4958_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(
    mut v_phase_4961_: *mut crate::leanh::LeanObject,
    mut v_x_4962_: *mut crate::leanh::LeanObject,
    mut v_a_4963_: *mut crate::leanh::LeanObject,
    mut v_a_4964_: *mut crate::leanh::LeanObject,
    mut v_a_4965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_4966_: u8 = 0;
    let mut v_res_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_4966_ = (crate::leanh::lean_unbox(v_phase_4961_) as u8);
    v_res_4967_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
        v_phase_boxed_4966_,
        v_x_4962_,
        v_a_4963_,
        v_a_4964_,
    );
    crate::leanh::lean_dec(v_a_4964_);
    crate::leanh::lean_dec_ref(v_a_4963_);
    return v_res_4967_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(
    mut v_00_u03b1_4968_: *mut crate::leanh::LeanObject,
    mut v_phase_4969_: u8,
    mut v_x_4970_: *mut crate::leanh::LeanObject,
    mut v_a_4971_: *mut crate::leanh::LeanObject,
    mut v_a_4972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4974_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
        v_phase_4969_,
        v_x_4970_,
        v_a_4971_,
        v_a_4972_,
    );
    return v___x_4974_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(
    mut v_00_u03b1_4975_: *mut crate::leanh::LeanObject,
    mut v_phase_4976_: *mut crate::leanh::LeanObject,
    mut v_x_4977_: *mut crate::leanh::LeanObject,
    mut v_a_4978_: *mut crate::leanh::LeanObject,
    mut v_a_4979_: *mut crate::leanh::LeanObject,
    mut v_a_4980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_4981_: u8 = 0;
    let mut v_res_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_4981_ = (crate::leanh::lean_unbox(v_phase_4976_) as u8);
    v_res_4982_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(
        v_00_u03b1_4975_,
        v_phase_boxed_4981_,
        v_x_4977_,
        v_a_4978_,
        v_a_4979_,
    );
    crate::leanh::lean_dec(v_a_4979_);
    crate::leanh::lean_dec_ref(v_a_4978_);
    return v_res_4982_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(
    mut v_pu_4983_: u8,
    mut v_decl_4984_: *mut crate::leanh::LeanObject,
    mut v___x_4985_: *mut crate::leanh::LeanObject,
    mut v___x_4986_: u8,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
    mut v___y_4988_: *mut crate::leanh::LeanObject,
    mut v___y_4989_: *mut crate::leanh::LeanObject,
    mut v___y_4990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4992_ = l_Lean_Compiler_LCNF_Decl_internalize(
                    v_pu_4983_,
                    v_decl_4984_,
                    v___x_4985_,
                    v___x_4986_,
                    v___y_4987_,
                    v___y_4988_,
                    v___y_4989_,
                    v___y_4990_,
                );
                if crate::leanh::lean_obj_tag(v___x_4992_) == 0 {
                    v_a_4993_ = crate::leanh::lean_ctor_get(v___x_4992_, 0);
                    crate::leanh::lean_inc(v_a_4993_);
                    crate::leanh::lean_dec_ref_known(v___x_4992_, 1);
                    v___x_4994_ = l_Lean_Compiler_LCNF_ppDecl(
                        v_pu_4983_,
                        v_a_4993_,
                        v___y_4987_,
                        v___y_4988_,
                        v___y_4989_,
                        v___y_4990_,
                    );
                    return v___x_4994_;
                } else {
                    v_a_4995_ = crate::leanh::lean_ctor_get(v___x_4992_, 0);
                    v_isSharedCheck_5002_ = (!crate::leanh::lean_is_exclusive(v___x_4992_)) as u8;
                    if v_isSharedCheck_5002_ == 0 {
                        v___x_4997_ = v___x_4992_;
                        v_isShared_4998_ = v_isSharedCheck_5002_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4995_);
                        crate::leanh::lean_dec(v___x_4992_);
                        v___x_4997_ = crate::leanh::lean_box(0);
                        v_isShared_4998_ = v_isSharedCheck_5002_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4998_ == 0 {
                    v___x_5000_ = v___x_4997_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5001_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
                    v___x_5000_ = v_reuseFailAlloc_5001_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(
    mut v_pu_5003_: *mut crate::leanh::LeanObject,
    mut v_decl_5004_: *mut crate::leanh::LeanObject,
    mut v___x_5005_: *mut crate::leanh::LeanObject,
    mut v___x_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
    mut v___y_5011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5012_: u8 = 0;
    let mut v___x_99__boxed_5013_: u8 = 0;
    let mut v_res_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5012_ = (crate::leanh::lean_unbox(v_pu_5003_) as u8);
    v___x_99__boxed_5013_ = (crate::leanh::lean_unbox(v___x_5006_) as u8);
    v_res_5014_ = l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(
        v_pu_boxed_5012_,
        v_decl_5004_,
        v___x_5005_,
        v___x_99__boxed_5013_,
        v___y_5007_,
        v___y_5008_,
        v___y_5009_,
        v___y_5010_,
    );
    crate::leanh::lean_dec(v___y_5010_);
    crate::leanh::lean_dec_ref(v___y_5009_);
    crate::leanh::lean_dec(v___y_5008_);
    crate::leanh::lean_dec_ref(v___y_5007_);
    return v_res_5014_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl_x27(
    mut v_pu_5015_: u8,
    mut v_decl_5016_: *mut crate::leanh::LeanObject,
    mut v_phase_5017_: u8,
    mut v_a_5018_: *mut crate::leanh::LeanObject,
    mut v_a_5019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: u8 = 0;
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5021_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1,
    );
    v___x_5022_ = 0;
    v___x_5023_ = crate::leanh::lean_box((v_pu_5015_) as usize);
    v___x_5024_ = crate::leanh::lean_box((v___x_5022_) as usize);
    v___f_5025_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5025_, 0, v___x_5023_);
    crate::leanh::lean_closure_set(v___f_5025_, 1, v_decl_5016_);
    crate::leanh::lean_closure_set(v___f_5025_, 2, v___x_5021_);
    crate::leanh::lean_closure_set(v___f_5025_, 3, v___x_5024_);
    v___x_5026_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
        v_phase_5017_,
        v___f_5025_,
        v_a_5018_,
        v_a_5019_,
    );
    return v___x_5026_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl_x27___boxed(
    mut v_pu_5027_: *mut crate::leanh::LeanObject,
    mut v_decl_5028_: *mut crate::leanh::LeanObject,
    mut v_phase_5029_: *mut crate::leanh::LeanObject,
    mut v_a_5030_: *mut crate::leanh::LeanObject,
    mut v_a_5031_: *mut crate::leanh::LeanObject,
    mut v_a_5032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5033_: u8 = 0;
    let mut v_phase_boxed_5034_: u8 = 0;
    let mut v_res_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5033_ = (crate::leanh::lean_unbox(v_pu_5027_) as u8);
    v_phase_boxed_5034_ = (crate::leanh::lean_unbox(v_phase_5029_) as u8);
    v_res_5035_ = l_Lean_Compiler_LCNF_ppDecl_x27(
        v_pu_boxed_5033_,
        v_decl_5028_,
        v_phase_boxed_5034_,
        v_a_5030_,
        v_a_5031_,
    );
    crate::leanh::lean_dec(v_a_5031_);
    crate::leanh::lean_dec_ref(v_a_5030_);
    return v_res_5035_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode_x27___lam__0(
    mut v_pu_5036_: u8,
    mut v_code_5037_: *mut crate::leanh::LeanObject,
    mut v___x_5038_: *mut crate::leanh::LeanObject,
    mut v___x_5039_: u8,
    mut v___y_5040_: *mut crate::leanh::LeanObject,
    mut v___y_5041_: *mut crate::leanh::LeanObject,
    mut v___y_5042_: *mut crate::leanh::LeanObject,
    mut v___y_5043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5045_ = l_Lean_Compiler_LCNF_Code_internalize(
                    v_pu_5036_,
                    v_code_5037_,
                    v___x_5038_,
                    v___x_5039_,
                    v___y_5040_,
                    v___y_5041_,
                    v___y_5042_,
                    v___y_5043_,
                );
                if crate::leanh::lean_obj_tag(v___x_5045_) == 0 {
                    v_a_5046_ = crate::leanh::lean_ctor_get(v___x_5045_, 0);
                    crate::leanh::lean_inc(v_a_5046_);
                    crate::leanh::lean_dec_ref_known(v___x_5045_, 1);
                    v___x_5047_ = l_Lean_Compiler_LCNF_ppCode(
                        v_pu_5036_,
                        v_a_5046_,
                        v___y_5040_,
                        v___y_5041_,
                        v___y_5042_,
                        v___y_5043_,
                    );
                    return v___x_5047_;
                } else {
                    v_a_5048_ = crate::leanh::lean_ctor_get(v___x_5045_, 0);
                    v_isSharedCheck_5055_ = (!crate::leanh::lean_is_exclusive(v___x_5045_)) as u8;
                    if v_isSharedCheck_5055_ == 0 {
                        v___x_5050_ = v___x_5045_;
                        v_isShared_5051_ = v_isSharedCheck_5055_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5048_);
                        crate::leanh::lean_dec(v___x_5045_);
                        v___x_5050_ = crate::leanh::lean_box(0);
                        v_isShared_5051_ = v_isSharedCheck_5055_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5051_ == 0 {
                    v___x_5053_ = v___x_5050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
                    v___x_5053_ = v_reuseFailAlloc_5054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(
    mut v_pu_5056_: *mut crate::leanh::LeanObject,
    mut v_code_5057_: *mut crate::leanh::LeanObject,
    mut v___x_5058_: *mut crate::leanh::LeanObject,
    mut v___x_5059_: *mut crate::leanh::LeanObject,
    mut v___y_5060_: *mut crate::leanh::LeanObject,
    mut v___y_5061_: *mut crate::leanh::LeanObject,
    mut v___y_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5065_: u8 = 0;
    let mut v___x_99__boxed_5066_: u8 = 0;
    let mut v_res_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5065_ = (crate::leanh::lean_unbox(v_pu_5056_) as u8);
    v___x_99__boxed_5066_ = (crate::leanh::lean_unbox(v___x_5059_) as u8);
    v_res_5067_ = l_Lean_Compiler_LCNF_ppCode_x27___lam__0(
        v_pu_boxed_5065_,
        v_code_5057_,
        v___x_5058_,
        v___x_99__boxed_5066_,
        v___y_5060_,
        v___y_5061_,
        v___y_5062_,
        v___y_5063_,
    );
    crate::leanh::lean_dec(v___y_5063_);
    crate::leanh::lean_dec_ref(v___y_5062_);
    crate::leanh::lean_dec(v___y_5061_);
    crate::leanh::lean_dec_ref(v___y_5060_);
    return v_res_5067_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode_x27(
    mut v_pu_5068_: u8,
    mut v_code_5069_: *mut crate::leanh::LeanObject,
    mut v_phase_5070_: u8,
    mut v_a_5071_: *mut crate::leanh::LeanObject,
    mut v_a_5072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: u8 = 0;
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5074_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1,
    );
    v___x_5075_ = 0;
    v___x_5076_ = crate::leanh::lean_box((v_pu_5068_) as usize);
    v___x_5077_ = crate::leanh::lean_box((v___x_5075_) as usize);
    v___f_5078_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5078_, 0, v___x_5076_);
    crate::leanh::lean_closure_set(v___f_5078_, 1, v_code_5069_);
    crate::leanh::lean_closure_set(v___f_5078_, 2, v___x_5074_);
    crate::leanh::lean_closure_set(v___f_5078_, 3, v___x_5077_);
    v___x_5079_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
        v_phase_5070_,
        v___f_5078_,
        v_a_5071_,
        v_a_5072_,
    );
    return v___x_5079_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode_x27___boxed(
    mut v_pu_5080_: *mut crate::leanh::LeanObject,
    mut v_code_5081_: *mut crate::leanh::LeanObject,
    mut v_phase_5082_: *mut crate::leanh::LeanObject,
    mut v_a_5083_: *mut crate::leanh::LeanObject,
    mut v_a_5084_: *mut crate::leanh::LeanObject,
    mut v_a_5085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5086_: u8 = 0;
    let mut v_phase_boxed_5087_: u8 = 0;
    let mut v_res_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5086_ = (crate::leanh::lean_unbox(v_pu_5080_) as u8);
    v_phase_boxed_5087_ = (crate::leanh::lean_unbox(v_phase_5082_) as u8);
    v_res_5088_ = l_Lean_Compiler_LCNF_ppCode_x27(
        v_pu_boxed_5086_,
        v_code_5081_,
        v_phase_boxed_5087_,
        v_a_5083_,
        v_a_5084_,
    );
    crate::leanh::lean_dec(v_a_5084_);
    crate::leanh::lean_dec_ref(v_a_5083_);
    return v_res_5088_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PrettyPrinter(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_PrettyPrinter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
}

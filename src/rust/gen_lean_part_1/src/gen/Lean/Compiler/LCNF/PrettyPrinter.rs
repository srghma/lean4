// Lean compiler output
// Module: Lean.Compiler.LCNF.PrettyPrinter
// Imports: Lean.PrettyPrinter.Delaborator.Options Lean.Compiler.LCNF.Internalize Init.Data.Format.Macro
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_to_int, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_length, lean_uint8_to_nat,
    lean_uint16_to_nat, lean_uint32_to_nat, lean_uint64_to_nat, lean_usize_add, lean_usize_dec_lt,
};
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
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 24) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [
        282574488338432 as *mut leanh::LeanObject,
        72621647814721793 as *mut leanh::LeanObject,
        65793 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1: u64 = 0;
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3_value:
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
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value:
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
    m_data: [95, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value:
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
    m_data: [40, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value:
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
    m_data: [41, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 116, 111, 114, 95, 0]};
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value: leanh::LeanStringObject<3> =
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
        m_data: [93, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20_value: leanh::LeanStringObject<
    1,
> = leanh::LeanStringObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__22_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__24_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__26_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__28_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value:
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
    m_data: [32, 58, 32, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2_value:
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
    m_data: [64, 38, 0],
};
static mut l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [124, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppAlt___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppAlt___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__11_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__15_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__17_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value: leanh::LeanStringObject<3> =
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
        m_data: [32, 91, 0],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__19_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__21_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__23_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__25_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__26_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__27_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__26_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__28_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__29_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__28_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__30_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__31_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__30_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__33_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__32_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__34_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__34_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__35_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__37_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__36_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__37_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__39_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__38_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__39_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__40_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__40: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__41_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__41_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppCode___closed__42_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__41_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppCode___closed__42: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppCode___closed__42_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_PP_run___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(
    mut v_f_2545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2546_ = l_Std_Format_indentD(v_f_2545_);
    return v___x_2546_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(
    mut v_f_2550_: *mut leanh::LeanObject,
    mut v_a_2551_: *mut leanh::LeanObject,
    mut v_b_2552_: *mut leanh::LeanObject,
    mut v___y_2553_: *mut leanh::LeanObject,
    mut v___y_2554_: *mut leanh::LeanObject,
    mut v___y_2555_: *mut leanh::LeanObject,
    mut v___y_2556_: *mut leanh::LeanObject,
    mut v___y_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2559_ = leanh::lean_ctor_get(v_a_2551_, 0);
                v_start_2560_ = leanh::lean_ctor_get(v_a_2551_, 1);
                v_stop_2561_ = leanh::lean_ctor_get(v_a_2551_, 2);
                v_isSharedCheck_2579_ = (!leanh::lean_is_exclusive(v_a_2551_)) as u8;
                if v_isSharedCheck_2579_ == 0 {
                    v___x_2563_ = v_a_2551_;
                    v_isShared_2564_ = v_isSharedCheck_2579_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_2561_);
                    leanh::lean_inc(v_start_2560_);
                    leanh::lean_inc(v_array_2559_);
                    leanh::lean_dec(v_a_2551_);
                    v___x_2563_ = leanh::lean_box(0);
                    v_isShared_2564_ = v_isSharedCheck_2579_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2565_ = lean_nat_dec_lt(v_start_2560_, v_stop_2561_);
                if v___x_2565_ == 0 {
                    leanh::lean_del_object(v___x_2563_);
                    leanh::lean_dec(v_stop_2561_);
                    leanh::lean_dec(v_start_2560_);
                    leanh::lean_dec_ref(v_array_2559_);
                    leanh::lean_dec_ref(v_f_2550_);
                    v___x_2566_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2566_, 0, v_b_2552_);
                    return v___x_2566_;
                } else {
                    v___x_2567_ = lean_array_fget_borrowed(v_array_2559_, v_start_2560_);
                    leanh::lean_inc_ref(v_f_2550_);
                    leanh::lean_inc(v___y_2557_);
                    leanh::lean_inc_ref(v___y_2556_);
                    leanh::lean_inc(v___y_2555_);
                    leanh::lean_inc_ref(v___y_2554_);
                    leanh::lean_inc_ref(v___y_2553_);
                    leanh::lean_inc(v___x_2567_);
                    v___x_2568_ = leanh::lean_apply_7(
                        v_f_2550_,
                        v___x_2567_,
                        v___y_2553_,
                        v___y_2554_,
                        v___y_2555_,
                        v___y_2556_,
                        v___y_2557_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2568_) == 0 {
                        v_a_2569_ = leanh::lean_ctor_get(v___x_2568_, 0);
                        leanh::lean_inc(v_a_2569_);
                        leanh::lean_dec_ref_known(v___x_2568_, 1);
                        v___x_2570_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2571_ = lean_nat_add(v_start_2560_, v___x_2570_);
                        leanh::lean_dec(v_start_2560_);
                        if v_isShared_2564_ == 0 {
                            leanh::lean_ctor_set(v___x_2563_, 1, v___x_2571_);
                            v___x_2573_ = v___x_2563_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2578_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_array_2559_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2571_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_stop_2561_);
                            v___x_2573_ = v_reuseFailAlloc_2578_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2563_);
                        leanh::lean_dec(v_stop_2561_);
                        leanh::lean_dec(v_start_2560_);
                        leanh::lean_dec_ref(v_array_2559_);
                        leanh::lean_dec(v_b_2552_);
                        leanh::lean_dec_ref(v_f_2550_);
                        return v___x_2568_;
                    }
                }
            }
            2 => {
                v___x_2574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_2575_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2575_, 0, v_b_2552_);
                leanh::lean_ctor_set(v___x_2575_, 1, v___x_2574_);
                v___x_2576_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2576_, 0, v___x_2575_);
                leanh::lean_ctor_set(v___x_2576_, 1, v_a_2569_);
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
    mut v_f_2580_: *mut leanh::LeanObject,
    mut v_a_2581_: *mut leanh::LeanObject,
    mut v_b_2582_: *mut leanh::LeanObject,
    mut v___y_2583_: *mut leanh::LeanObject,
    mut v___y_2584_: *mut leanh::LeanObject,
    mut v___y_2585_: *mut leanh::LeanObject,
    mut v___y_2586_: *mut leanh::LeanObject,
    mut v___y_2587_: *mut leanh::LeanObject,
    mut v___y_2588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2589_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_2580_, v_a_2581_, v_b_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
    leanh::lean_dec(v___y_2587_);
    leanh::lean_dec_ref(v___y_2586_);
    leanh::lean_dec(v___y_2585_);
    leanh::lean_dec_ref(v___y_2584_);
    leanh::lean_dec_ref(v___y_2583_);
    return v_res_2589_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(
    mut v_as_2590_: *mut leanh::LeanObject,
    mut v_f_2591_: *mut leanh::LeanObject,
    mut v_a_2592_: *mut leanh::LeanObject,
    mut v_a_2593_: *mut leanh::LeanObject,
    mut v_a_2594_: *mut leanh::LeanObject,
    mut v_a_2595_: *mut leanh::LeanObject,
    mut v_a_2596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: u8 = 0;
    v___x_2598_ = leanh::lean_unsigned_to_nat(0);
    v___x_2599_ = lean_array_get_size(v_as_2590_);
    v___x_2600_ = lean_nat_dec_lt(v___x_2598_, v___x_2599_);
    if v___x_2600_ == 0 {
        let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_f_2591_);
        leanh::lean_dec_ref(v_as_2590_);
        v___x_2601_ = leanh::lean_box(0);
        v___x_2602_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2602_, 0, v___x_2601_);
        return v___x_2602_;
    } else {
        let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2603_ = lean_array_fget_borrowed(v_as_2590_, v___x_2598_);
        leanh::lean_inc_ref(v_f_2591_);
        leanh::lean_inc(v_a_2596_);
        leanh::lean_inc_ref(v_a_2595_);
        leanh::lean_inc(v_a_2594_);
        leanh::lean_inc_ref(v_a_2593_);
        leanh::lean_inc_ref(v_a_2592_);
        leanh::lean_inc(v___x_2603_);
        v___x_2604_ = leanh::lean_apply_7(
            v_f_2591_,
            v___x_2603_,
            v_a_2592_,
            v_a_2593_,
            v_a_2594_,
            v_a_2595_,
            v_a_2596_,
            leanh::lean_box(0),
        );
        if leanh::lean_obj_tag(v___x_2604_) == 0 {
            let mut v_a_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2605_ = leanh::lean_ctor_get(v___x_2604_, 0);
            leanh::lean_inc(v_a_2605_);
            leanh::lean_dec_ref_known(v___x_2604_, 1);
            v___x_2606_ = leanh::lean_unsigned_to_nat(1);
            v___x_2607_ = l_Array_toSubarray___redArg(v_as_2590_, v___x_2606_, v___x_2599_);
            v___x_2608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_2591_, v___x_2607_, v_a_2605_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
            return v___x_2608_;
        } else {
            leanh::lean_dec_ref(v_f_2591_);
            leanh::lean_dec_ref(v_as_2590_);
            return v___x_2604_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg___boxed(
    mut v_as_2609_: *mut leanh::LeanObject,
    mut v_f_2610_: *mut leanh::LeanObject,
    mut v_a_2611_: *mut leanh::LeanObject,
    mut v_a_2612_: *mut leanh::LeanObject,
    mut v_a_2613_: *mut leanh::LeanObject,
    mut v_a_2614_: *mut leanh::LeanObject,
    mut v_a_2615_: *mut leanh::LeanObject,
    mut v_a_2616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2617_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(
            v_as_2609_, v_f_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_,
        );
    leanh::lean_dec(v_a_2615_);
    leanh::lean_dec_ref(v_a_2614_);
    leanh::lean_dec(v_a_2613_);
    leanh::lean_dec_ref(v_a_2612_);
    leanh::lean_dec_ref(v_a_2611_);
    return v_res_2617_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(
    mut v_00_u03b1_2618_: *mut leanh::LeanObject,
    mut v_as_2619_: *mut leanh::LeanObject,
    mut v_f_2620_: *mut leanh::LeanObject,
    mut v_a_2621_: *mut leanh::LeanObject,
    mut v_a_2622_: *mut leanh::LeanObject,
    mut v_a_2623_: *mut leanh::LeanObject,
    mut v_a_2624_: *mut leanh::LeanObject,
    mut v_a_2625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2627_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(
            v_as_2619_, v_f_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_,
        );
    return v___x_2627_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___boxed(
    mut v_00_u03b1_2628_: *mut leanh::LeanObject,
    mut v_as_2629_: *mut leanh::LeanObject,
    mut v_f_2630_: *mut leanh::LeanObject,
    mut v_a_2631_: *mut leanh::LeanObject,
    mut v_a_2632_: *mut leanh::LeanObject,
    mut v_a_2633_: *mut leanh::LeanObject,
    mut v_a_2634_: *mut leanh::LeanObject,
    mut v_a_2635_: *mut leanh::LeanObject,
    mut v_a_2636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2635_);
    leanh::lean_dec_ref(v_a_2634_);
    leanh::lean_dec(v_a_2633_);
    leanh::lean_dec_ref(v_a_2632_);
    leanh::lean_dec_ref(v_a_2631_);
    return v_res_2637_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(
    mut v_00_u03b1_2638_: *mut leanh::LeanObject,
    mut v_f_2639_: *mut leanh::LeanObject,
    mut v_inst_2640_: *mut leanh::LeanObject,
    mut v_R_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
    mut v_b_2643_: *mut leanh::LeanObject,
    mut v_c_2644_: *mut leanh::LeanObject,
    mut v___y_2645_: *mut leanh::LeanObject,
    mut v___y_2646_: *mut leanh::LeanObject,
    mut v___y_2647_: *mut leanh::LeanObject,
    mut v___y_2648_: *mut leanh::LeanObject,
    mut v___y_2649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(v_f_2639_, v_a_2642_, v_b_2643_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
    return v___x_2651_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___boxed(
    mut v_00_u03b1_2652_: *mut leanh::LeanObject,
    mut v_f_2653_: *mut leanh::LeanObject,
    mut v_inst_2654_: *mut leanh::LeanObject,
    mut v_R_2655_: *mut leanh::LeanObject,
    mut v_a_2656_: *mut leanh::LeanObject,
    mut v_b_2657_: *mut leanh::LeanObject,
    mut v_c_2658_: *mut leanh::LeanObject,
    mut v___y_2659_: *mut leanh::LeanObject,
    mut v___y_2660_: *mut leanh::LeanObject,
    mut v___y_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
    mut v___y_2663_: *mut leanh::LeanObject,
    mut v___y_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2665_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(v_00_u03b1_2652_, v_f_2653_, v_inst_2654_, v_R_2655_, v_a_2656_, v_b_2657_, v_c_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
    leanh::lean_dec(v___y_2663_);
    leanh::lean_dec_ref(v___y_2662_);
    leanh::lean_dec(v___y_2661_);
    leanh::lean_dec_ref(v___y_2660_);
    leanh::lean_dec_ref(v___y_2659_);
    return v_res_2665_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(
    mut v_f_2666_: *mut leanh::LeanObject,
    mut v_pre_2667_: *mut leanh::LeanObject,
    mut v_as_2668_: *mut leanh::LeanObject,
    mut v_sz_2669_: usize,
    mut v_i_2670_: usize,
    mut v_b_2671_: *mut leanh::LeanObject,
    mut v___y_2672_: *mut leanh::LeanObject,
    mut v___y_2673_: *mut leanh::LeanObject,
    mut v___y_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
    mut v___y_2676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: usize = 0;
    let mut v___x_2686_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2678_ = lean_usize_dec_lt(v_i_2670_, v_sz_2669_);
                if v___x_2678_ == 0 {
                    leanh::lean_dec(v_pre_2667_);
                    leanh::lean_dec_ref(v_f_2666_);
                    v___x_2679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2679_, 0, v_b_2671_);
                    return v___x_2679_;
                } else {
                    v_a_2680_ = lean_array_uget_borrowed(v_as_2668_, v_i_2670_);
                    leanh::lean_inc_ref(v_f_2666_);
                    leanh::lean_inc(v___y_2676_);
                    leanh::lean_inc_ref(v___y_2675_);
                    leanh::lean_inc(v___y_2674_);
                    leanh::lean_inc_ref(v___y_2673_);
                    leanh::lean_inc_ref(v___y_2672_);
                    leanh::lean_inc(v_a_2680_);
                    v___x_2681_ = leanh::lean_apply_7(
                        v_f_2666_,
                        v_a_2680_,
                        v___y_2672_,
                        v___y_2673_,
                        v___y_2674_,
                        v___y_2675_,
                        v___y_2676_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2681_) == 0 {
                        v_a_2682_ = leanh::lean_ctor_get(v___x_2681_, 0);
                        leanh::lean_inc(v_a_2682_);
                        leanh::lean_dec_ref_known(v___x_2681_, 1);
                        leanh::lean_inc(v_pre_2667_);
                        v___x_2683_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2683_, 0, v_b_2671_);
                        leanh::lean_ctor_set(v___x_2683_, 1, v_pre_2667_);
                        v___x_2684_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2684_, 0, v___x_2683_);
                        leanh::lean_ctor_set(v___x_2684_, 1, v_a_2682_);
                        v___x_2685_ = 1usize;
                        v___x_2686_ = lean_usize_add(v_i_2670_, v___x_2685_);
                        v_i_2670_ = v___x_2686_;
                        v_b_2671_ = v___x_2684_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_b_2671_);
                        leanh::lean_dec(v_pre_2667_);
                        leanh::lean_dec_ref(v_f_2666_);
                        return v___x_2681_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg___boxed(
    mut v_f_2688_: *mut leanh::LeanObject,
    mut v_pre_2689_: *mut leanh::LeanObject,
    mut v_as_2690_: *mut leanh::LeanObject,
    mut v_sz_2691_: *mut leanh::LeanObject,
    mut v_i_2692_: *mut leanh::LeanObject,
    mut v_b_2693_: *mut leanh::LeanObject,
    mut v___y_2694_: *mut leanh::LeanObject,
    mut v___y_2695_: *mut leanh::LeanObject,
    mut v___y_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
    mut v___y_2698_: *mut leanh::LeanObject,
    mut v___y_2699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2700_: usize = 0;
    let mut v_i_boxed_2701_: usize = 0;
    let mut v_res_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2700_ = leanh::lean_unbox_usize(v_sz_2691_);
    leanh::lean_dec(v_sz_2691_);
    v_i_boxed_2701_ = leanh::lean_unbox_usize(v_i_2692_);
    leanh::lean_dec(v_i_2692_);
    v_res_2702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_2688_, v_pre_2689_, v_as_2690_, v_sz_boxed_2700_, v_i_boxed_2701_, v_b_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
    leanh::lean_dec(v___y_2698_);
    leanh::lean_dec_ref(v___y_2697_);
    leanh::lean_dec(v___y_2696_);
    leanh::lean_dec_ref(v___y_2695_);
    leanh::lean_dec_ref(v___y_2694_);
    leanh::lean_dec_ref(v_as_2690_);
    return v_res_2702_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(
    mut v_pre_2703_: *mut leanh::LeanObject,
    mut v_as_2704_: *mut leanh::LeanObject,
    mut v_f_2705_: *mut leanh::LeanObject,
    mut v_a_2706_: *mut leanh::LeanObject,
    mut v_a_2707_: *mut leanh::LeanObject,
    mut v_a_2708_: *mut leanh::LeanObject,
    mut v_a_2709_: *mut leanh::LeanObject,
    mut v_a_2710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2713_: usize = 0;
    let mut v___x_2714_: usize = 0;
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_result_2712_ = leanh::lean_box(0);
    v_sz_2713_ = lean_array_size(v_as_2704_);
    v___x_2714_ = 0usize;
    v___x_2715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_2705_, v_pre_2703_, v_as_2704_, v_sz_2713_, v___x_2714_, v_result_2712_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
    return v___x_2715_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg___boxed(
    mut v_pre_2716_: *mut leanh::LeanObject,
    mut v_as_2717_: *mut leanh::LeanObject,
    mut v_f_2718_: *mut leanh::LeanObject,
    mut v_a_2719_: *mut leanh::LeanObject,
    mut v_a_2720_: *mut leanh::LeanObject,
    mut v_a_2721_: *mut leanh::LeanObject,
    mut v_a_2722_: *mut leanh::LeanObject,
    mut v_a_2723_: *mut leanh::LeanObject,
    mut v_a_2724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2723_);
    leanh::lean_dec_ref(v_a_2722_);
    leanh::lean_dec(v_a_2721_);
    leanh::lean_dec_ref(v_a_2720_);
    leanh::lean_dec_ref(v_a_2719_);
    leanh::lean_dec_ref(v_as_2717_);
    return v_res_2725_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(
    mut v_00_u03b1_2726_: *mut leanh::LeanObject,
    mut v_pre_2727_: *mut leanh::LeanObject,
    mut v_as_2728_: *mut leanh::LeanObject,
    mut v_f_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
    mut v_a_2731_: *mut leanh::LeanObject,
    mut v_a_2732_: *mut leanh::LeanObject,
    mut v_a_2733_: *mut leanh::LeanObject,
    mut v_a_2734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2737_: *mut leanh::LeanObject,
    mut v_pre_2738_: *mut leanh::LeanObject,
    mut v_as_2739_: *mut leanh::LeanObject,
    mut v_f_2740_: *mut leanh::LeanObject,
    mut v_a_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
    mut v_a_2744_: *mut leanh::LeanObject,
    mut v_a_2745_: *mut leanh::LeanObject,
    mut v_a_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2745_);
    leanh::lean_dec_ref(v_a_2744_);
    leanh::lean_dec(v_a_2743_);
    leanh::lean_dec_ref(v_a_2742_);
    leanh::lean_dec_ref(v_a_2741_);
    leanh::lean_dec_ref(v_as_2739_);
    return v_res_2747_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(
    mut v_00_u03b1_2748_: *mut leanh::LeanObject,
    mut v_f_2749_: *mut leanh::LeanObject,
    mut v_pre_2750_: *mut leanh::LeanObject,
    mut v_as_2751_: *mut leanh::LeanObject,
    mut v_sz_2752_: usize,
    mut v_i_2753_: usize,
    mut v_b_2754_: *mut leanh::LeanObject,
    mut v___y_2755_: *mut leanh::LeanObject,
    mut v___y_2756_: *mut leanh::LeanObject,
    mut v___y_2757_: *mut leanh::LeanObject,
    mut v___y_2758_: *mut leanh::LeanObject,
    mut v___y_2759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(v_f_2749_, v_pre_2750_, v_as_2751_, v_sz_2752_, v_i_2753_, v_b_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
    return v___x_2761_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___boxed(
    mut v_00_u03b1_2762_: *mut leanh::LeanObject,
    mut v_f_2763_: *mut leanh::LeanObject,
    mut v_pre_2764_: *mut leanh::LeanObject,
    mut v_as_2765_: *mut leanh::LeanObject,
    mut v_sz_2766_: *mut leanh::LeanObject,
    mut v_i_2767_: *mut leanh::LeanObject,
    mut v_b_2768_: *mut leanh::LeanObject,
    mut v___y_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
    mut v___y_2771_: *mut leanh::LeanObject,
    mut v___y_2772_: *mut leanh::LeanObject,
    mut v___y_2773_: *mut leanh::LeanObject,
    mut v___y_2774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2775_: usize = 0;
    let mut v_i_boxed_2776_: usize = 0;
    let mut v_res_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2775_ = leanh::lean_unbox_usize(v_sz_2766_);
    leanh::lean_dec(v_sz_2766_);
    v_i_boxed_2776_ = leanh::lean_unbox_usize(v_i_2767_);
    leanh::lean_dec(v_i_2767_);
    v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(v_00_u03b1_2762_, v_f_2763_, v_pre_2764_, v_as_2765_, v_sz_boxed_2775_, v_i_boxed_2776_, v_b_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
    leanh::lean_dec(v___y_2773_);
    leanh::lean_dec_ref(v___y_2772_);
    leanh::lean_dec(v___y_2771_);
    leanh::lean_dec_ref(v___y_2770_);
    leanh::lean_dec_ref(v___y_2769_);
    leanh::lean_dec_ref(v_as_2765_);
    return v_res_2777_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
    mut v_fvarId_2778_: *mut leanh::LeanObject,
    mut v_a_2779_: *mut leanh::LeanObject,
    mut v_a_2780_: *mut leanh::LeanObject,
    mut v_a_2781_: *mut leanh::LeanObject,
    mut v_a_2782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: u8 = 0;
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut v_a_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v___y_2801_: u8 = 0;
    let mut v___x_2802_: u8 = 0;
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: u8 = 0;
    let mut v___x_2812_: u8 = 0;
    let mut v_isSharedCheck_2813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_fvarId_2778_);
                v___x_2784_ = l_Lean_Compiler_LCNF_getBinderName(
                    v_fvarId_2778_,
                    v_a_2779_,
                    v_a_2780_,
                    v_a_2781_,
                    v_a_2782_,
                );
                if leanh::lean_obj_tag(v___x_2784_) == 0 {
                    leanh::lean_dec(v_fvarId_2778_);
                    v_a_2785_ = leanh::lean_ctor_get(v___x_2784_, 0);
                    v_isSharedCheck_2795_ = (!leanh::lean_is_exclusive(v___x_2784_)) as u8;
                    if v_isSharedCheck_2795_ == 0 {
                        v___x_2787_ = v___x_2784_;
                        v_isShared_2788_ = v_isSharedCheck_2795_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2785_);
                        leanh::lean_dec(v___x_2784_);
                        v___x_2787_ = leanh::lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_2795_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2796_ = leanh::lean_ctor_get(v___x_2784_, 0);
                    v_isSharedCheck_2813_ = (!leanh::lean_is_exclusive(v___x_2784_)) as u8;
                    if v_isSharedCheck_2813_ == 0 {
                        v___x_2798_ = v___x_2784_;
                        v_isShared_2799_ = v_isSharedCheck_2813_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2796_);
                        leanh::lean_dec(v___x_2784_);
                        v___x_2798_ = leanh::lean_box(0);
                        v_isShared_2799_ = v_isSharedCheck_2813_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2789_ = 1;
                v___x_2790_ = l_Lean_Name_toString(v_a_2785_, v___x_2789_);
                v___x_2791_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2791_, 0, v___x_2790_);
                if v_isShared_2788_ == 0 {
                    leanh::lean_ctor_set(v___x_2787_, 0, v___x_2791_);
                    v___x_2793_ = v___x_2787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
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
                    leanh::lean_inc(v_a_2796_);
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
                    leanh::lean_dec(v_a_2796_);
                    v___x_2802_ = 1;
                    v___x_2803_ = l_Lean_Name_toString(v_fvarId_2778_, v___x_2802_);
                    v___x_2804_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2804_, 0, v___x_2803_);
                    if v_isShared_2799_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2798_, 0);
                        leanh::lean_ctor_set(v___x_2798_, 0, v___x_2804_);
                        v___x_2806_ = v___x_2798_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
                        v___x_2806_ = v_reuseFailAlloc_2807_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fvarId_2778_);
                    if v_isShared_2799_ == 0 {
                        v___x_2809_ = v___x_2798_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2810_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2796_);
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
    mut v_fvarId_2814_: *mut leanh::LeanObject,
    mut v_a_2815_: *mut leanh::LeanObject,
    mut v_a_2816_: *mut leanh::LeanObject,
    mut v_a_2817_: *mut leanh::LeanObject,
    mut v_a_2818_: *mut leanh::LeanObject,
    mut v_a_2819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2820_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
        v_fvarId_2814_,
        v_a_2815_,
        v_a_2816_,
        v_a_2817_,
        v_a_2818_,
    );
    leanh::lean_dec(v_a_2818_);
    leanh::lean_dec_ref(v_a_2817_);
    leanh::lean_dec(v_a_2816_);
    leanh::lean_dec_ref(v_a_2815_);
    return v_res_2820_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppFVar(
    mut v_fvarId_2821_: *mut leanh::LeanObject,
    mut v_a_2822_: *mut leanh::LeanObject,
    mut v_a_2823_: *mut leanh::LeanObject,
    mut v_a_2824_: *mut leanh::LeanObject,
    mut v_a_2825_: *mut leanh::LeanObject,
    mut v_a_2826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_fvarId_2829_: *mut leanh::LeanObject,
    mut v_a_2830_: *mut leanh::LeanObject,
    mut v_a_2831_: *mut leanh::LeanObject,
    mut v_a_2832_: *mut leanh::LeanObject,
    mut v_a_2833_: *mut leanh::LeanObject,
    mut v_a_2834_: *mut leanh::LeanObject,
    mut v_a_2835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_Lean_Compiler_LCNF_PP_ppFVar(
        v_fvarId_2829_,
        v_a_2830_,
        v_a_2831_,
        v_a_2832_,
        v_a_2833_,
        v_a_2834_,
    );
    leanh::lean_dec(v_a_2834_);
    leanh::lean_dec_ref(v_a_2833_);
    leanh::lean_dec(v_a_2832_);
    leanh::lean_dec_ref(v_a_2831_);
    leanh::lean_dec_ref(v_a_2830_);
    return v_res_2836_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1() -> u64 {
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: u64 = 0;
    v___x_2843_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0;
    v___x_2844_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2843_);
    return v___x_2844_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2845_: u64 = 0;
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2845_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1,
    );
    v___x_2846_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0;
    v___x_2847_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_2847_, 0, v___x_2846_);
    leanh::lean_ctor_set_uint64(
        v___x_2847_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2845_,
    );
    return v___x_2847_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2850_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2850_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2851_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4,
    );
    v___x_2852_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2852_, 0, v___x_2851_);
    return v___x_2852_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2853_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5,
    );
    v___x_2854_ = leanh::lean_unsigned_to_nat(0);
    v___x_2855_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2855_, 0, v___x_2854_);
    leanh::lean_ctor_set(v___x_2855_, 1, v___x_2854_);
    leanh::lean_ctor_set(v___x_2855_, 2, v___x_2854_);
    leanh::lean_ctor_set(v___x_2855_, 3, v___x_2854_);
    leanh::lean_ctor_set(v___x_2855_, 4, v___x_2853_);
    leanh::lean_ctor_set(v___x_2855_, 5, v___x_2853_);
    leanh::lean_ctor_set(v___x_2855_, 6, v___x_2853_);
    leanh::lean_ctor_set(v___x_2855_, 7, v___x_2853_);
    leanh::lean_ctor_set(v___x_2855_, 8, v___x_2853_);
    leanh::lean_ctor_set(v___x_2855_, 9, v___x_2853_);
    return v___x_2855_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2856_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5,
    );
    v___x_2857_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2857_, 0, v___x_2856_);
    leanh::lean_ctor_set(v___x_2857_, 1, v___x_2856_);
    leanh::lean_ctor_set(v___x_2857_, 2, v___x_2856_);
    leanh::lean_ctor_set(v___x_2857_, 3, v___x_2856_);
    leanh::lean_ctor_set(v___x_2857_, 4, v___x_2856_);
    leanh::lean_ctor_set(v___x_2857_, 5, v___x_2856_);
    return v___x_2857_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2858_ = leanh::lean_unsigned_to_nat(32);
    v___x_2859_ = lean_mk_empty_array_with_capacity(v___x_2858_);
    v___x_2860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2860_, 0, v___x_2859_);
    return v___x_2860_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2861_: usize = 0;
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2861_ = 5usize;
    v___x_2862_ = leanh::lean_unsigned_to_nat(0);
    v___x_2863_ = leanh::lean_unsigned_to_nat(32);
    v___x_2864_ = lean_mk_empty_array_with_capacity(v___x_2863_);
    v___x_2865_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8,
    );
    v___x_2866_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2866_, 0, v___x_2865_);
    leanh::lean_ctor_set(v___x_2866_, 1, v___x_2864_);
    leanh::lean_ctor_set(v___x_2866_, 2, v___x_2862_);
    leanh::lean_ctor_set(v___x_2866_, 3, v___x_2862_);
    leanh::lean_ctor_set_usize(v___x_2866_, 4, v___x_2861_);
    return v___x_2866_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2867_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5,
    );
    v___x_2868_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2868_, 0, v___x_2867_);
    leanh::lean_ctor_set(v___x_2868_, 1, v___x_2867_);
    leanh::lean_ctor_set(v___x_2868_, 2, v___x_2867_);
    leanh::lean_ctor_set(v___x_2868_, 3, v___x_2867_);
    leanh::lean_ctor_set(v___x_2868_, 4, v___x_2867_);
    return v___x_2868_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__10,
    );
    v___x_2870_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9,
    );
    v___x_2871_ = leanh::lean_box(1);
    v___x_2872_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7,
    );
    v___x_2873_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6_once),
        _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6,
    );
    v___x_2874_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2874_, 0, v___x_2873_);
    leanh::lean_ctor_set(v___x_2874_, 1, v___x_2872_);
    leanh::lean_ctor_set(v___x_2874_, 2, v___x_2871_);
    leanh::lean_ctor_set(v___x_2874_, 3, v___x_2870_);
    leanh::lean_ctor_set(v___x_2874_, 4, v___x_2869_);
    return v___x_2874_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
    mut v_e_2875_: *mut leanh::LeanObject,
    mut v_a_2876_: *mut leanh::LeanObject,
    mut v_a_2877_: *mut leanh::LeanObject,
    mut v_a_2878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    let mut v___x_2882_: u8 = 0;
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2894_: u8 = 0;
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2880_ = leanh::lean_box(1);
                v___x_2881_ = 0;
                v___x_2882_ = 1;
                v___x_2883_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2,
                );
                v___x_2884_ = leanh::lean_unsigned_to_nat(0);
                v___x_2885_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3;
                v___x_2886_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_a_2876_);
                v___x_2887_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2887_, 0, v___x_2883_);
                leanh::lean_ctor_set(v___x_2887_, 1, v___x_2880_);
                leanh::lean_ctor_set(v___x_2887_, 2, v_a_2876_);
                leanh::lean_ctor_set(v___x_2887_, 3, v___x_2885_);
                leanh::lean_ctor_set(v___x_2887_, 4, v___x_2886_);
                leanh::lean_ctor_set(v___x_2887_, 5, v___x_2884_);
                leanh::lean_ctor_set(v___x_2887_, 6, v___x_2886_);
                leanh::lean_ctor_set_uint8(
                    v___x_2887_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v___x_2881_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2887_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_2881_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2887_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_2881_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2887_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_2882_,
                );
                v___x_2888_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11_once
                    ),
                    _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__11,
                );
                v___x_2889_ = lean_st_mk_ref(v___x_2888_);
                v___x_2890_ =
                    l_Lean_Meta_ppExpr(v_e_2875_, v___x_2887_, v___x_2889_, v_a_2877_, v_a_2878_);
                leanh::lean_dec_ref_known(v___x_2887_, 7);
                if leanh::lean_obj_tag(v___x_2890_) == 0 {
                    v_a_2891_ = leanh::lean_ctor_get(v___x_2890_, 0);
                    v_isSharedCheck_2899_ = (!leanh::lean_is_exclusive(v___x_2890_)) as u8;
                    if v_isSharedCheck_2899_ == 0 {
                        v___x_2893_ = v___x_2890_;
                        v_isShared_2894_ = v_isSharedCheck_2899_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2891_);
                        leanh::lean_dec(v___x_2890_);
                        v___x_2893_ = leanh::lean_box(0);
                        v_isShared_2894_ = v_isSharedCheck_2899_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2889_);
                    return v___x_2890_;
                }
            }
            1 => {
                v___x_2895_ = lean_st_ref_get(v___x_2889_);
                leanh::lean_dec(v___x_2889_);
                leanh::lean_dec(v___x_2895_);
                if v_isShared_2894_ == 0 {
                    v___x_2897_ = v___x_2893_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2898_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2891_);
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
    mut v_e_2900_: *mut leanh::LeanObject,
    mut v_a_2901_: *mut leanh::LeanObject,
    mut v_a_2902_: *mut leanh::LeanObject,
    mut v_a_2903_: *mut leanh::LeanObject,
    mut v_a_2904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2905_ =
        l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
    leanh::lean_dec(v_a_2903_);
    leanh::lean_dec_ref(v_a_2902_);
    leanh::lean_dec_ref(v_a_2901_);
    return v_res_2905_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppExpr(
    mut v_e_2906_: *mut leanh::LeanObject,
    mut v_a_2907_: *mut leanh::LeanObject,
    mut v_a_2908_: *mut leanh::LeanObject,
    mut v_a_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_a_2911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2913_ =
        l_Lean_Compiler_LCNF_PP_ppExpr___redArg(v_e_2906_, v_a_2907_, v_a_2910_, v_a_2911_);
    return v___x_2913_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppExpr___boxed(
    mut v_e_2914_: *mut leanh::LeanObject,
    mut v_a_2915_: *mut leanh::LeanObject,
    mut v_a_2916_: *mut leanh::LeanObject,
    mut v_a_2917_: *mut leanh::LeanObject,
    mut v_a_2918_: *mut leanh::LeanObject,
    mut v_a_2919_: *mut leanh::LeanObject,
    mut v_a_2920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Lean_Compiler_LCNF_PP_ppExpr(
        v_e_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_,
    );
    leanh::lean_dec(v_a_2919_);
    leanh::lean_dec_ref(v_a_2918_);
    leanh::lean_dec(v_a_2917_);
    leanh::lean_dec_ref(v_a_2916_);
    leanh::lean_dec_ref(v_a_2915_);
    return v_res_2921_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
    mut v_opts_2922_: *mut leanh::LeanObject,
    mut v_opt_2923_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2924_ = leanh::lean_ctor_get(v_opt_2923_, 0);
    v_defValue_2925_ = leanh::lean_ctor_get(v_opt_2923_, 1);
    v_map_2926_ = leanh::lean_ctor_get(v_opts_2922_, 0);
    v___x_2927_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2926_,
            v_name_2924_,
        );
    if leanh::lean_obj_tag(v___x_2927_) == 0 {
        let mut v___x_2928_: u8 = 0;
        v___x_2928_ = (leanh::lean_unbox(v_defValue_2925_) as u8);
        return v___x_2928_;
    } else {
        let mut v_val_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2929_ = leanh::lean_ctor_get(v___x_2927_, 0);
        leanh::lean_inc(v_val_2929_);
        leanh::lean_dec_ref_known(v___x_2927_, 1);
        if leanh::lean_obj_tag(v_val_2929_) == 1 {
            let mut v_v_2930_: u8 = 0;
            v_v_2930_ = leanh::lean_ctor_get_uint8(v_val_2929_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2929_, 0);
            return v_v_2930_;
        } else {
            let mut v___x_2931_: u8 = 0;
            leanh::lean_dec(v_val_2929_);
            v___x_2931_ = (leanh::lean_unbox(v_defValue_2925_) as u8);
            return v___x_2931_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(
    mut v_opts_2932_: *mut leanh::LeanObject,
    mut v_opt_2933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2934_: u8 = 0;
    let mut v_r_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2934_ =
        l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(v_opts_2932_, v_opt_2933_);
    leanh::lean_dec_ref(v_opt_2933_);
    leanh::lean_dec_ref(v_opts_2932_);
    v_r_2935_ = leanh::lean_box((v_res_2934_) as usize);
    return v_r_2935_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(
    mut v_a_2936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2937_ = lean_nat_to_int(v_a_2936_);
    return v___x_2937_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2946_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4;
    v___x_2947_ = lean_string_length(v___x_2946_);
    return v___x_2947_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2948_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6_once),
        _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6,
    );
    v___x_2949_ = lean_nat_to_int(v___x_2948_);
    return v___x_2949_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArg___redArg(
    mut v_e_2954_: *mut leanh::LeanObject,
    mut v_a_2955_: *mut leanh::LeanObject,
    mut v_a_2956_: *mut leanh::LeanObject,
    mut v_a_2957_: *mut leanh::LeanObject,
    mut v_a_2958_: *mut leanh::LeanObject,
    mut v_a_2959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2968_: u8 = 0;
    let mut v_options_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: u8 = 0;
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: u8 = 0;
    let mut v___x_2979_: u8 = 0;
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2984_: u8 = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_2954_) {
                0 => {
                    v___x_2961_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1;
                    v___x_2962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2962_, 0, v___x_2961_);
                    return v___x_2962_;
                }
                1 => {
                    v_fvarId_2963_ = leanh::lean_ctor_get(v_e_2954_, 0);
                    leanh::lean_inc(v_fvarId_2963_);
                    leanh::lean_dec_ref_known(v_e_2954_, 1);
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
                    v_expr_2965_ = leanh::lean_ctor_get(v_e_2954_, 0);
                    v_isSharedCheck_3001_ = (!leanh::lean_is_exclusive(v_e_2954_)) as u8;
                    if v_isSharedCheck_3001_ == 0 {
                        v___x_2967_ = v_e_2954_;
                        v_isShared_2968_ = v_isSharedCheck_3001_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_expr_2965_);
                        leanh::lean_dec(v_e_2954_);
                        v___x_2967_ = leanh::lean_box(0);
                        v_isShared_2968_ = v_isSharedCheck_3001_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v_options_2969_ = leanh::lean_ctor_get(v_a_2958_, 2);
                v___x_2970_ = l_Lean_pp_explicit;
                v___x_2971_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                    v_options_2969_,
                    v___x_2970_,
                );
                if v___x_2971_ == 0 {
                    leanh::lean_dec_ref(v_expr_2965_);
                    v___x_2972_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3;
                    if v_isShared_2968_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2967_, 0);
                        leanh::lean_ctor_set(v___x_2967_, 0, v___x_2972_);
                        v___x_2974_ = v___x_2967_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2975_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
                        v___x_2974_ = v_reuseFailAlloc_2975_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2967_);
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
                                    if leanh::lean_obj_tag(v___x_2980_) == 0 {
                                        v_a_2981_ = leanh::lean_ctor_get(v___x_2980_, 0);
                                        v_isSharedCheck_2996_ =
                                            (!leanh::lean_is_exclusive(v___x_2980_)) as u8;
                                        if v_isSharedCheck_2996_ == 0 {
                                            v___x_2983_ = v___x_2980_;
                                            v_isShared_2984_ = v_isSharedCheck_2996_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2981_);
                                            leanh::lean_dec(v___x_2980_);
                                            v___x_2983_ = leanh::lean_box(0);
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
                v___x_2985_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once
                    ),
                    _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7,
                );
                v___x_2986_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8;
                v___x_2987_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2987_, 0, v___x_2986_);
                leanh::lean_ctor_set(v___x_2987_, 1, v_a_2981_);
                v___x_2988_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9;
                v___x_2989_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2989_, 0, v___x_2987_);
                leanh::lean_ctor_set(v___x_2989_, 1, v___x_2988_);
                v___x_2990_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2990_, 0, v___x_2985_);
                leanh::lean_ctor_set(v___x_2990_, 1, v___x_2989_);
                v___x_2991_ = 0;
                v___x_2992_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2992_, 0, v___x_2990_);
                leanh::lean_ctor_set_uint8(
                    v___x_2992_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2991_,
                );
                if v_isShared_2984_ == 0 {
                    leanh::lean_ctor_set(v___x_2983_, 0, v___x_2992_);
                    v___x_2994_ = v___x_2983_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2995_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
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
    mut v_e_3002_: *mut leanh::LeanObject,
    mut v_a_3003_: *mut leanh::LeanObject,
    mut v_a_3004_: *mut leanh::LeanObject,
    mut v_a_3005_: *mut leanh::LeanObject,
    mut v_a_3006_: *mut leanh::LeanObject,
    mut v_a_3007_: *mut leanh::LeanObject,
    mut v_a_3008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3009_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(
        v_e_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_,
    );
    leanh::lean_dec(v_a_3007_);
    leanh::lean_dec_ref(v_a_3006_);
    leanh::lean_dec(v_a_3005_);
    leanh::lean_dec_ref(v_a_3004_);
    leanh::lean_dec_ref(v_a_3003_);
    return v_res_3009_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArg(
    mut v_pu_3010_: u8,
    mut v_e_3011_: *mut leanh::LeanObject,
    mut v_a_3012_: *mut leanh::LeanObject,
    mut v_a_3013_: *mut leanh::LeanObject,
    mut v_a_3014_: *mut leanh::LeanObject,
    mut v_a_3015_: *mut leanh::LeanObject,
    mut v_a_3016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3018_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(
        v_e_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_,
    );
    return v___x_3018_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArg___boxed(
    mut v_pu_3019_: *mut leanh::LeanObject,
    mut v_e_3020_: *mut leanh::LeanObject,
    mut v_a_3021_: *mut leanh::LeanObject,
    mut v_a_3022_: *mut leanh::LeanObject,
    mut v_a_3023_: *mut leanh::LeanObject,
    mut v_a_3024_: *mut leanh::LeanObject,
    mut v_a_3025_: *mut leanh::LeanObject,
    mut v_a_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_3027_: u8 = 0;
    let mut v_res_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3027_ = (leanh::lean_unbox(v_pu_3019_) as u8);
    v_res_3028_ = l_Lean_Compiler_LCNF_PP_ppArg(
        v_pu_boxed_3027_,
        v_e_3020_,
        v_a_3021_,
        v_a_3022_,
        v_a_3023_,
        v_a_3024_,
        v_a_3025_,
    );
    leanh::lean_dec(v_a_3025_);
    leanh::lean_dec_ref(v_a_3024_);
    leanh::lean_dec(v_a_3023_);
    leanh::lean_dec_ref(v_a_3022_);
    leanh::lean_dec_ref(v_a_3021_);
    return v_res_3028_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppArgs(
    mut v_pu_3029_: u8,
    mut v_args_3030_: *mut leanh::LeanObject,
    mut v_a_3031_: *mut leanh::LeanObject,
    mut v_a_3032_: *mut leanh::LeanObject,
    mut v_a_3033_: *mut leanh::LeanObject,
    mut v_a_3034_: *mut leanh::LeanObject,
    mut v_a_3035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3037_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
    v___x_3038_ = leanh::lean_box((v_pu_3029_) as usize);
    v___x_3039_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PP_ppArg___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    leanh::lean_closure_set(v___x_3039_, 0, v___x_3038_);
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
    mut v_pu_3041_: *mut leanh::LeanObject,
    mut v_args_3042_: *mut leanh::LeanObject,
    mut v_a_3043_: *mut leanh::LeanObject,
    mut v_a_3044_: *mut leanh::LeanObject,
    mut v_a_3045_: *mut leanh::LeanObject,
    mut v_a_3046_: *mut leanh::LeanObject,
    mut v_a_3047_: *mut leanh::LeanObject,
    mut v_a_3048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_3049_: u8 = 0;
    let mut v_res_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3049_ = (leanh::lean_unbox(v_pu_3041_) as u8);
    v_res_3050_ = l_Lean_Compiler_LCNF_PP_ppArgs(
        v_pu_boxed_3049_,
        v_args_3042_,
        v_a_3043_,
        v_a_3044_,
        v_a_3045_,
        v_a_3046_,
        v_a_3047_,
    );
    leanh::lean_dec(v_a_3047_);
    leanh::lean_dec_ref(v_a_3046_);
    leanh::lean_dec(v_a_3045_);
    leanh::lean_dec_ref(v_a_3044_);
    leanh::lean_dec_ref(v_a_3043_);
    leanh::lean_dec_ref(v_args_3042_);
    return v_res_3050_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(
    mut v_lit_3051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_3054_: u64 = 0;
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut v_val_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut v_val_3079_: u8 = 0;
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3084_: u16 = 0;
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3089_: u32 = 0;
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3094_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_lit_3051_) {
                0 => {
                    v_val_3059_ = leanh::lean_ctor_get(v_lit_3051_, 0);
                    v_isSharedCheck_3068_ = (!leanh::lean_is_exclusive(v_lit_3051_)) as u8;
                    if v_isSharedCheck_3068_ == 0 {
                        v___x_3061_ = v_lit_3051_;
                        v_isShared_3062_ = v_isSharedCheck_3068_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3059_);
                        leanh::lean_dec(v_lit_3051_);
                        v___x_3061_ = leanh::lean_box(0);
                        v_isShared_3062_ = v_isSharedCheck_3068_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_val_3069_ = leanh::lean_ctor_get(v_lit_3051_, 0);
                    v_isSharedCheck_3078_ = (!leanh::lean_is_exclusive(v_lit_3051_)) as u8;
                    if v_isSharedCheck_3078_ == 0 {
                        v___x_3071_ = v_lit_3051_;
                        v_isShared_3072_ = v_isSharedCheck_3078_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3069_);
                        leanh::lean_dec(v_lit_3051_);
                        v___x_3071_ = leanh::lean_box(0);
                        v_isShared_3072_ = v_isSharedCheck_3078_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_val_3079_ = leanh::lean_ctor_get_uint8(v_lit_3051_, 0 as u32);
                    leanh::lean_dec_ref_known(v_lit_3051_, 0);
                    v___x_3080_ = lean_uint8_to_nat(v_val_3079_);
                    v___x_3081_ = l_Nat_reprFast(v___x_3080_);
                    v___x_3082_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3082_, 0, v___x_3081_);
                    v___x_3083_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3083_, 0, v___x_3082_);
                    return v___x_3083_;
                }
                3 => {
                    v_val_3084_ = leanh::lean_ctor_get_uint16(v_lit_3051_, 0 as u32);
                    leanh::lean_dec_ref_known(v_lit_3051_, 0);
                    v___x_3085_ = lean_uint16_to_nat(v_val_3084_);
                    v___x_3086_ = l_Nat_reprFast(v___x_3085_);
                    v___x_3087_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3087_, 0, v___x_3086_);
                    v___x_3088_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3088_, 0, v___x_3087_);
                    return v___x_3088_;
                }
                4 => {
                    v_val_3089_ = leanh::lean_ctor_get_uint32(v_lit_3051_, 0 as u32);
                    leanh::lean_dec_ref_known(v_lit_3051_, 0);
                    v___x_3090_ = lean_uint32_to_nat(v_val_3089_);
                    v___x_3091_ = l_Nat_reprFast(v___x_3090_);
                    v___x_3092_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3092_, 0, v___x_3091_);
                    v___x_3093_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3093_, 0, v___x_3092_);
                    return v___x_3093_;
                }
                _ => {
                    v_val_3094_ = leanh::lean_ctor_get_uint64(v_lit_3051_, 0 as u32);
                    leanh::lean_dec_ref(v_lit_3051_);
                    v_v_3054_ = v_val_3094_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_3055_ = lean_uint64_to_nat(v_v_3054_);
                v___x_3056_ = l_Nat_reprFast(v___x_3055_);
                v___x_3057_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3057_, 0, v___x_3056_);
                v___x_3058_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3058_, 0, v___x_3057_);
                return v___x_3058_;
            }
            2 => {
                v___x_3063_ = l_Nat_reprFast(v_val_3059_);
                if v_isShared_3062_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3061_, 3);
                    leanh::lean_ctor_set(v___x_3061_, 0, v___x_3063_);
                    v___x_3065_ = v___x_3061_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3067_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3063_);
                    v___x_3065_ = v_reuseFailAlloc_3067_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3066_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3066_, 0, v___x_3065_);
                return v___x_3066_;
            }
            4 => {
                v___x_3073_ = l_String_quote(v_val_3069_);
                if v_isShared_3072_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3071_, 3);
                    leanh::lean_ctor_set(v___x_3071_, 0, v___x_3073_);
                    v___x_3075_ = v___x_3071_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3077_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3073_);
                    v___x_3075_ = v_reuseFailAlloc_3077_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3076_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3076_, 0, v___x_3075_);
                return v___x_3076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(
    mut v_lit_3095_: *mut leanh::LeanObject,
    mut v_a_3096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3097_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_3095_);
    return v_res_3097_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLitValue(
    mut v_lit_3098_: *mut leanh::LeanObject,
    mut v_a_3099_: *mut leanh::LeanObject,
    mut v_a_3100_: *mut leanh::LeanObject,
    mut v_a_3101_: *mut leanh::LeanObject,
    mut v_a_3102_: *mut leanh::LeanObject,
    mut v_a_3103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_lit_3098_);
    return v___x_3105_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(
    mut v_lit_3106_: *mut leanh::LeanObject,
    mut v_a_3107_: *mut leanh::LeanObject,
    mut v_a_3108_: *mut leanh::LeanObject,
    mut v_a_3109_: *mut leanh::LeanObject,
    mut v_a_3110_: *mut leanh::LeanObject,
    mut v_a_3111_: *mut leanh::LeanObject,
    mut v_a_3112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3113_ = l_Lean_Compiler_LCNF_PP_ppLitValue(
        v_lit_3106_,
        v_a_3107_,
        v_a_3108_,
        v_a_3109_,
        v_a_3110_,
        v_a_3111_,
    );
    leanh::lean_dec(v_a_3111_);
    leanh::lean_dec_ref(v_a_3110_);
    leanh::lean_dec(v_a_3109_);
    leanh::lean_dec_ref(v_a_3108_);
    leanh::lean_dec_ref(v_a_3107_);
    return v_res_3113_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(
    mut v_x_3126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3148_: u8 = 0;
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: u8 = 0;
    let mut v___x_3160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3127_ = leanh::lean_ctor_get(v_x_3126_, 0);
                leanh::lean_inc(v_name_3127_);
                v_cidx_3128_ = leanh::lean_ctor_get(v_x_3126_, 1);
                leanh::lean_inc(v_cidx_3128_);
                v_usize_3129_ = leanh::lean_ctor_get(v_x_3126_, 3);
                leanh::lean_inc(v_usize_3129_);
                v_ssize_3130_ = leanh::lean_ctor_get(v_x_3126_, 4);
                leanh::lean_inc(v_ssize_3130_);
                leanh::lean_dec_ref(v_x_3126_);
                v___x_3143_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5;
                v___x_3144_ = l_Nat_reprFast(v_cidx_3128_);
                v___x_3145_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3145_, 0, v___x_3144_);
                v_r_3146_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v_r_3146_, 0, v___x_3143_);
                leanh::lean_ctor_set(v_r_3146_, 1, v___x_3145_);
                v___x_3158_ = leanh::lean_unsigned_to_nat(0);
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
                v___x_3133_ = leanh::lean_box(0);
                v___x_3134_ = lean_name_eq(v_name_3127_, v___x_3133_);
                if v___x_3134_ == 0 {
                    v___x_3135_ = 1;
                    v___x_3136_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1;
                    v___x_3137_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3137_, 0, v_r_3132_);
                    leanh::lean_ctor_set(v___x_3137_, 1, v___x_3136_);
                    v___x_3138_ = l_Lean_Name_toString(v_name_3127_, v___x_3135_);
                    v___x_3139_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3139_, 0, v___x_3138_);
                    v___x_3140_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3140_, 0, v___x_3137_);
                    leanh::lean_ctor_set(v___x_3140_, 1, v___x_3139_);
                    v___x_3141_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3;
                    v_r_3142_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_r_3142_, 0, v___x_3140_);
                    leanh::lean_ctor_set(v_r_3142_, 1, v___x_3141_);
                    return v_r_3142_;
                } else {
                    leanh::lean_dec(v_name_3127_);
                    return v_r_3132_;
                }
            }
            2 => {
                if v___y_3148_ == 0 {
                    leanh::lean_dec(v_ssize_3130_);
                    leanh::lean_dec(v_usize_3129_);
                    v_r_3132_ = v_r_3146_;
                    state = 1;
                    continue;
                } else {
                    v___x_3149_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7;
                    v___x_3150_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3150_, 0, v_r_3146_);
                    leanh::lean_ctor_set(v___x_3150_, 1, v___x_3149_);
                    v___x_3151_ = l_Nat_reprFast(v_usize_3129_);
                    v___x_3152_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3152_, 0, v___x_3151_);
                    v___x_3153_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3153_, 0, v___x_3150_);
                    leanh::lean_ctor_set(v___x_3153_, 1, v___x_3152_);
                    v___x_3154_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3154_, 0, v___x_3153_);
                    leanh::lean_ctor_set(v___x_3154_, 1, v___x_3149_);
                    v___x_3155_ = l_Nat_reprFast(v_ssize_3130_);
                    v___x_3156_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
                    v_r_3157_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_r_3157_, 0, v___x_3154_);
                    leanh::lean_ctor_set(v_r_3157_, 1, v___x_3156_);
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
    mut v_a_3161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3162_ =
        l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(
            v_a_3161_,
        );
    return v___x_3162_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLetValue(
    mut v_pu_3210_: u8,
    mut v_e_3211_: *mut leanh::LeanObject,
    mut v_a_3212_: *mut leanh::LeanObject,
    mut v_a_3213_: *mut leanh::LeanObject,
    mut v_a_3214_: *mut leanh::LeanObject,
    mut v_a_3215_: *mut leanh::LeanObject,
    mut v_a_3216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_value_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3228_: u8 = 0;
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut v_declName_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut v_fvarId_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_i_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_i_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3297_: u8 = 0;
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3302_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3315_: u8 = 0;
    let mut v_isSharedCheck_3316_: u8 = 0;
    let mut v_i_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3321_: u8 = 0;
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3339_: u8 = 0;
    let mut v_isSharedCheck_3340_: u8 = 0;
    let mut v_n_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_fn_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_isSharedCheck_3385_: u8 = 0;
    let mut v_fn_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3390_: u8 = 0;
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3395_: u8 = 0;
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3407_: u8 = 0;
    let mut v_isSharedCheck_3408_: u8 = 0;
    let mut v_n_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3418_: u8 = 0;
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3431_: u8 = 0;
    let mut v_isSharedCheck_3432_: u8 = 0;
    let mut v_var_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_3435_: u8 = 0;
    let mut v_args_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3461_: u8 = 0;
    let mut v_fvarId_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3470_: u8 = 0;
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v_isSharedCheck_3479_: u8 = 0;
    let mut v_unused_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3492_: u8 = 0;
    let mut v_fvarId_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_3211_) {
                0 => {
                    v_value_3218_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    leanh::lean_inc_ref(v_value_3218_);
                    leanh::lean_dec_ref_known(v_e_3211_, 1);
                    v___x_3219_ = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(v_value_3218_);
                    return v___x_3219_;
                }
                1 => {
                    v___x_3220_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1;
                    v___x_3221_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3221_, 0, v___x_3220_);
                    return v___x_3221_;
                }
                2 => {
                    v_idx_3222_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    leanh::lean_inc(v_idx_3222_);
                    v_struct_3223_ = leanh::lean_ctor_get(v_e_3211_, 2);
                    leanh::lean_inc(v_struct_3223_);
                    leanh::lean_dec_ref_known(v_e_3211_, 3);
                    v___x_3224_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_struct_3223_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if leanh::lean_obj_tag(v___x_3224_) == 0 {
                        v_a_3225_ = leanh::lean_ctor_get(v___x_3224_, 0);
                        v_isSharedCheck_3237_ =
                            (!leanh::lean_is_exclusive(v___x_3224_)) as u8;
                        if v_isSharedCheck_3237_ == 0 {
                            v___x_3227_ = v___x_3224_;
                            v_isShared_3228_ = v_isSharedCheck_3237_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3225_);
                            leanh::lean_dec(v___x_3224_);
                            v___x_3227_ = leanh::lean_box(0);
                            v_isShared_3228_ = v_isSharedCheck_3237_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_idx_3222_);
                        return v___x_3224_;
                    }
                }
                3 => {
                    v_declName_3238_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    leanh::lean_inc(v_declName_3238_);
                    v_us_3239_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    leanh::lean_inc(v_us_3239_);
                    v_args_3240_ = leanh::lean_ctor_get(v_e_3211_, 2);
                    leanh::lean_inc_ref(v_args_3240_);
                    leanh::lean_dec_ref_known(v_e_3211_, 3);
                    v___x_3241_ = l_Lean_Expr_const___override(v_declName_3238_, v_us_3239_);
                    v___x_3242_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                        v___x_3241_,
                        v_a_3212_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if leanh::lean_obj_tag(v___x_3242_) == 0 {
                        v_a_3243_ = leanh::lean_ctor_get(v___x_3242_, 0);
                        leanh::lean_inc(v_a_3243_);
                        leanh::lean_dec_ref_known(v___x_3242_, 1);
                        v___x_3244_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                            v_pu_3210_,
                            v_args_3240_,
                            v_a_3212_,
                            v_a_3213_,
                            v_a_3214_,
                            v_a_3215_,
                            v_a_3216_,
                        );
                        leanh::lean_dec_ref(v_args_3240_);
                        if leanh::lean_obj_tag(v___x_3244_) == 0 {
                            v_a_3245_ = leanh::lean_ctor_get(v___x_3244_, 0);
                            v_isSharedCheck_3253_ =
                                (!leanh::lean_is_exclusive(v___x_3244_)) as u8;
                            if v_isSharedCheck_3253_ == 0 {
                                v___x_3247_ = v___x_3244_;
                                v_isShared_3248_ = v_isSharedCheck_3253_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3245_);
                                leanh::lean_dec(v___x_3244_);
                                v___x_3247_ = leanh::lean_box(0);
                                v_isShared_3248_ = v_isSharedCheck_3253_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3243_);
                            return v___x_3244_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_args_3240_);
                        return v___x_3242_;
                    }
                }
                4 => {
                    v_fvarId_3254_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    v_args_3255_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3273_ = (!leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3273_ == 0 {
                        v___x_3257_ = v_e_3211_;
                        v_isShared_3258_ = v_isSharedCheck_3273_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_args_3255_);
                        leanh::lean_inc(v_fvarId_3254_);
                        leanh::lean_dec(v_e_3211_);
                        v___x_3257_ = leanh::lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3273_;
                        state = 5;
                        continue;
                    }
                }
                5 => {
                    v_i_3274_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    v_args_3275_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3292_ = (!leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3292_ == 0 {
                        v___x_3277_ = v_e_3211_;
                        v_isShared_3278_ = v_isSharedCheck_3292_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_args_3275_);
                        leanh::lean_inc(v_i_3274_);
                        leanh::lean_dec(v_e_3211_);
                        v___x_3277_ = leanh::lean_box(0);
                        v_isShared_3278_ = v_isSharedCheck_3292_;
                        state = 9;
                        continue;
                    }
                }
                6 => {
                    v_i_3293_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    v_var_3294_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3316_ = (!leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3316_ == 0 {
                        v___x_3296_ = v_e_3211_;
                        v_isShared_3297_ = v_isSharedCheck_3316_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_var_3294_);
                        leanh::lean_inc(v_i_3293_);
                        leanh::lean_dec(v_e_3211_);
                        v___x_3296_ = leanh::lean_box(0);
                        v_isShared_3297_ = v_isSharedCheck_3316_;
                        state = 13;
                        continue;
                    }
                }
                7 => {
                    v_i_3317_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    v_var_3318_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3340_ = (!leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3340_ == 0 {
                        v___x_3320_ = v_e_3211_;
                        v_isShared_3321_ = v_isSharedCheck_3340_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_var_3318_);
                        leanh::lean_inc(v_i_3317_);
                        leanh::lean_dec(v_e_3211_);
                        v___x_3320_ = leanh::lean_box(0);
                        v_isShared_3321_ = v_isSharedCheck_3340_;
                        state = 17;
                        continue;
                    }
                }
                8 => {
                    v_n_3341_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    leanh::lean_inc(v_n_3341_);
                    v_offset_3342_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    leanh::lean_inc(v_offset_3342_);
                    v_var_3343_ = leanh::lean_ctor_get(v_e_3211_, 2);
                    leanh::lean_inc(v_var_3343_);
                    leanh::lean_dec_ref_known(v_e_3211_, 3);
                    v___x_3344_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_var_3343_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if leanh::lean_obj_tag(v___x_3344_) == 0 {
                        v_a_3345_ = leanh::lean_ctor_get(v___x_3344_, 0);
                        v_isSharedCheck_3364_ =
                            (!leanh::lean_is_exclusive(v___x_3344_)) as u8;
                        if v_isSharedCheck_3364_ == 0 {
                            v___x_3347_ = v___x_3344_;
                            v_isShared_3348_ = v_isSharedCheck_3364_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3345_);
                            leanh::lean_dec(v___x_3344_);
                            v___x_3347_ = leanh::lean_box(0);
                            v_isShared_3348_ = v_isSharedCheck_3364_;
                            state = 21;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_offset_3342_);
                        leanh::lean_dec(v_n_3341_);
                        return v___x_3344_;
                    }
                }
                9 => {
                    v_fn_3365_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    v_args_3366_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3385_ = (!leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3385_ == 0 {
                        v___x_3368_ = v_e_3211_;
                        v_isShared_3369_ = v_isSharedCheck_3385_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_args_3366_);
                        leanh::lean_inc(v_fn_3365_);
                        leanh::lean_dec(v_e_3211_);
                        v___x_3368_ = leanh::lean_box(0);
                        v_isShared_3369_ = v_isSharedCheck_3385_;
                        state = 23;
                        continue;
                    }
                }
                10 => {
                    v_fn_3386_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    v_args_3387_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3408_ = (!leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3408_ == 0 {
                        v___x_3389_ = v_e_3211_;
                        v_isShared_3390_ = v_isSharedCheck_3408_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_args_3387_);
                        leanh::lean_inc(v_fn_3386_);
                        leanh::lean_dec(v_e_3211_);
                        v___x_3389_ = leanh::lean_box(0);
                        v_isShared_3390_ = v_isSharedCheck_3408_;
                        state = 27;
                        continue;
                    }
                }
                11 => {
                    v_n_3409_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    v_var_3410_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3432_ = (!leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3432_ == 0 {
                        v___x_3412_ = v_e_3211_;
                        v_isShared_3413_ = v_isSharedCheck_3432_;
                        state = 31;
                        continue;
                    } else {
                        leanh::lean_inc(v_var_3410_);
                        leanh::lean_inc(v_n_3409_);
                        leanh::lean_dec(v_e_3211_);
                        v___x_3412_ = leanh::lean_box(0);
                        v_isShared_3413_ = v_isSharedCheck_3432_;
                        state = 31;
                        continue;
                    }
                }
                12 => {
                    v_var_3433_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    leanh::lean_inc(v_var_3433_);
                    v_i_3434_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    leanh::lean_inc_ref(v_i_3434_);
                    v_updateHeader_3435_ = leanh::lean_ctor_get_uint8(
                        v_e_3211_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_args_3436_ = leanh::lean_ctor_get(v_e_3211_, 2);
                    leanh::lean_inc_ref(v_args_3436_);
                    leanh::lean_dec_ref_known(v_e_3211_, 3);
                    v___x_3437_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_var_3433_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if leanh::lean_obj_tag(v___x_3437_) == 0 {
                        v_a_3438_ = leanh::lean_ctor_get(v___x_3437_, 0);
                        leanh::lean_inc(v_a_3438_);
                        leanh::lean_dec_ref_known(v___x_3437_, 1);
                        v___x_3439_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                            v_pu_3210_,
                            v_args_3436_,
                            v_a_3212_,
                            v_a_3213_,
                            v_a_3214_,
                            v_a_3215_,
                            v_a_3216_,
                        );
                        leanh::lean_dec_ref(v_args_3436_);
                        if leanh::lean_obj_tag(v___x_3439_) == 0 {
                            v_a_3440_ = leanh::lean_ctor_get(v___x_3439_, 0);
                            v_isSharedCheck_3461_ =
                                (!leanh::lean_is_exclusive(v___x_3439_)) as u8;
                            if v_isSharedCheck_3461_ == 0 {
                                v___x_3442_ = v___x_3439_;
                                v_isShared_3443_ = v_isSharedCheck_3461_;
                                state = 35;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3440_);
                                leanh::lean_dec(v___x_3439_);
                                v___x_3442_ = leanh::lean_box(0);
                                v_isShared_3443_ = v_isSharedCheck_3461_;
                                state = 35;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3438_);
                            leanh::lean_dec_ref(v_i_3434_);
                            return v___x_3439_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_args_3436_);
                        leanh::lean_dec_ref(v_i_3434_);
                        return v___x_3437_;
                    }
                }
                13 => {
                    v_fvarId_3462_ = leanh::lean_ctor_get(v_e_3211_, 1);
                    v_isSharedCheck_3479_ = (!leanh::lean_is_exclusive(v_e_3211_)) as u8;
                    if v_isSharedCheck_3479_ == 0 {
                        v_unused_3480_ = leanh::lean_ctor_get(v_e_3211_, 0);
                        leanh::lean_dec(v_unused_3480_);
                        v___x_3464_ = v_e_3211_;
                        v_isShared_3465_ = v_isSharedCheck_3479_;
                        state = 38;
                        continue;
                    } else {
                        leanh::lean_inc(v_fvarId_3462_);
                        leanh::lean_dec(v_e_3211_);
                        v___x_3464_ = leanh::lean_box(0);
                        v_isShared_3465_ = v_isSharedCheck_3479_;
                        state = 38;
                        continue;
                    }
                }
                14 => {
                    v_fvarId_3481_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    leanh::lean_inc(v_fvarId_3481_);
                    leanh::lean_dec_ref_known(v_e_3211_, 1);
                    v___x_3482_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_3481_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if leanh::lean_obj_tag(v___x_3482_) == 0 {
                        v_a_3483_ = leanh::lean_ctor_get(v___x_3482_, 0);
                        v_isSharedCheck_3492_ =
                            (!leanh::lean_is_exclusive(v___x_3482_)) as u8;
                        if v_isSharedCheck_3492_ == 0 {
                            v___x_3485_ = v___x_3482_;
                            v_isShared_3486_ = v_isSharedCheck_3492_;
                            state = 42;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3483_);
                            leanh::lean_dec(v___x_3482_);
                            v___x_3485_ = leanh::lean_box(0);
                            v_isShared_3486_ = v_isSharedCheck_3492_;
                            state = 42;
                            continue;
                        }
                    } else {
                        return v___x_3482_;
                    }
                }
                _ => {
                    v_fvarId_3493_ = leanh::lean_ctor_get(v_e_3211_, 0);
                    leanh::lean_inc(v_fvarId_3493_);
                    leanh::lean_dec_ref_known(v_e_3211_, 1);
                    v___x_3494_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_3493_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    if leanh::lean_obj_tag(v___x_3494_) == 0 {
                        v_a_3495_ = leanh::lean_ctor_get(v___x_3494_, 0);
                        v_isSharedCheck_3504_ =
                            (!leanh::lean_is_exclusive(v___x_3494_)) as u8;
                        if v_isSharedCheck_3504_ == 0 {
                            v___x_3497_ = v___x_3494_;
                            v_isShared_3498_ = v_isSharedCheck_3504_;
                            state = 44;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3495_);
                            leanh::lean_dec(v___x_3494_);
                            v___x_3497_ = leanh::lean_box(0);
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
                v___x_3230_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3230_, 0, v_a_3225_);
                leanh::lean_ctor_set(v___x_3230_, 1, v___x_3229_);
                v___x_3231_ = l_Nat_reprFast(v_idx_3222_);
                v___x_3232_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3232_, 0, v___x_3231_);
                v___x_3233_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3233_, 0, v___x_3230_);
                leanh::lean_ctor_set(v___x_3233_, 1, v___x_3232_);
                if v_isShared_3228_ == 0 {
                    leanh::lean_ctor_set(v___x_3227_, 0, v___x_3233_);
                    v___x_3235_ = v___x_3227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3233_);
                    v___x_3235_ = v_reuseFailAlloc_3236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3235_;
            }
            3 => {
                v___x_3249_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3249_, 0, v_a_3243_);
                leanh::lean_ctor_set(v___x_3249_, 1, v_a_3245_);
                if v_isShared_3248_ == 0 {
                    leanh::lean_ctor_set(v___x_3247_, 0, v___x_3249_);
                    v___x_3251_ = v___x_3247_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
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
                if leanh::lean_obj_tag(v___x_3259_) == 0 {
                    v_a_3260_ = leanh::lean_ctor_get(v___x_3259_, 0);
                    leanh::lean_inc(v_a_3260_);
                    leanh::lean_dec_ref_known(v___x_3259_, 1);
                    v___x_3261_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                        v_pu_3210_,
                        v_args_3255_,
                        v_a_3212_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                        v_a_3216_,
                    );
                    leanh::lean_dec_ref(v_args_3255_);
                    if leanh::lean_obj_tag(v___x_3261_) == 0 {
                        v_a_3262_ = leanh::lean_ctor_get(v___x_3261_, 0);
                        v_isSharedCheck_3272_ =
                            (!leanh::lean_is_exclusive(v___x_3261_)) as u8;
                        if v_isSharedCheck_3272_ == 0 {
                            v___x_3264_ = v___x_3261_;
                            v_isShared_3265_ = v_isSharedCheck_3272_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3262_);
                            leanh::lean_dec(v___x_3261_);
                            v___x_3264_ = leanh::lean_box(0);
                            v_isShared_3265_ = v_isSharedCheck_3272_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3260_);
                        leanh::lean_del_object(v___x_3257_);
                        return v___x_3261_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3257_);
                    leanh::lean_dec_ref(v_args_3255_);
                    return v___x_3259_;
                }
            }
            6 => {
                if v_isShared_3258_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3257_, 5);
                    leanh::lean_ctor_set(v___x_3257_, 1, v_a_3262_);
                    leanh::lean_ctor_set(v___x_3257_, 0, v_a_3260_);
                    v___x_3267_ = v___x_3257_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3271_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_a_3262_);
                    v___x_3267_ = v_reuseFailAlloc_3271_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3265_ == 0 {
                    leanh::lean_ctor_set(v___x_3264_, 0, v___x_3267_);
                    v___x_3269_ = v___x_3264_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
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
                leanh::lean_dec_ref(v_args_3275_);
                if leanh::lean_obj_tag(v___x_3279_) == 0 {
                    v_a_3280_ = leanh::lean_ctor_get(v___x_3279_, 0);
                    v_isSharedCheck_3291_ = (!leanh::lean_is_exclusive(v___x_3279_)) as u8;
                    if v_isSharedCheck_3291_ == 0 {
                        v___x_3282_ = v___x_3279_;
                        v_isShared_3283_ = v_isSharedCheck_3291_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3280_);
                        leanh::lean_dec(v___x_3279_);
                        v___x_3282_ = leanh::lean_box(0);
                        v_isShared_3283_ = v_isSharedCheck_3291_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3277_);
                    leanh::lean_dec_ref(v_i_3274_);
                    return v___x_3279_;
                }
            }
            10 => {
                v___x_3284_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_3274_);
                if v_isShared_3278_ == 0 {
                    leanh::lean_ctor_set(v___x_3277_, 1, v_a_3280_);
                    leanh::lean_ctor_set(v___x_3277_, 0, v___x_3284_);
                    v___x_3286_ = v___x_3277_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_a_3280_);
                    v___x_3286_ = v_reuseFailAlloc_3290_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3283_ == 0 {
                    leanh::lean_ctor_set(v___x_3282_, 0, v___x_3286_);
                    v___x_3288_ = v___x_3282_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
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
                if leanh::lean_obj_tag(v___x_3298_) == 0 {
                    v_a_3299_ = leanh::lean_ctor_get(v___x_3298_, 0);
                    v_isSharedCheck_3315_ = (!leanh::lean_is_exclusive(v___x_3298_)) as u8;
                    if v_isSharedCheck_3315_ == 0 {
                        v___x_3301_ = v___x_3298_;
                        v_isShared_3302_ = v_isSharedCheck_3315_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3299_);
                        leanh::lean_dec(v___x_3298_);
                        v___x_3301_ = leanh::lean_box(0);
                        v_isShared_3302_ = v_isSharedCheck_3315_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3296_);
                    leanh::lean_dec(v_i_3293_);
                    return v___x_3298_;
                }
            }
            14 => {
                v___x_3303_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3;
                v___x_3304_ = l_Nat_reprFast(v_i_3293_);
                v___x_3305_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3305_, 0, v___x_3304_);
                if v_isShared_3297_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3296_, 5);
                    leanh::lean_ctor_set(v___x_3296_, 1, v___x_3305_);
                    leanh::lean_ctor_set(v___x_3296_, 0, v___x_3303_);
                    v___x_3307_ = v___x_3296_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3314_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___x_3305_);
                    v___x_3307_ = v_reuseFailAlloc_3314_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3308_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5;
                v___x_3309_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3309_, 0, v___x_3307_);
                leanh::lean_ctor_set(v___x_3309_, 1, v___x_3308_);
                v___x_3310_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3310_, 0, v___x_3309_);
                leanh::lean_ctor_set(v___x_3310_, 1, v_a_3299_);
                if v_isShared_3302_ == 0 {
                    leanh::lean_ctor_set(v___x_3301_, 0, v___x_3310_);
                    v___x_3312_ = v___x_3301_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3313_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
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
                if leanh::lean_obj_tag(v___x_3322_) == 0 {
                    v_a_3323_ = leanh::lean_ctor_get(v___x_3322_, 0);
                    v_isSharedCheck_3339_ = (!leanh::lean_is_exclusive(v___x_3322_)) as u8;
                    if v_isSharedCheck_3339_ == 0 {
                        v___x_3325_ = v___x_3322_;
                        v_isShared_3326_ = v_isSharedCheck_3339_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3323_);
                        leanh::lean_dec(v___x_3322_);
                        v___x_3325_ = leanh::lean_box(0);
                        v_isShared_3326_ = v_isSharedCheck_3339_;
                        state = 18;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3320_);
                    leanh::lean_dec(v_i_3317_);
                    return v___x_3322_;
                }
            }
            18 => {
                v___x_3327_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7;
                v___x_3328_ = l_Nat_reprFast(v_i_3317_);
                v___x_3329_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3329_, 0, v___x_3328_);
                if v_isShared_3321_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3320_, 5);
                    leanh::lean_ctor_set(v___x_3320_, 1, v___x_3329_);
                    leanh::lean_ctor_set(v___x_3320_, 0, v___x_3327_);
                    v___x_3331_ = v___x_3320_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3338_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3338_, 1, v___x_3329_);
                    v___x_3331_ = v_reuseFailAlloc_3338_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_3332_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5;
                v___x_3333_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3333_, 0, v___x_3331_);
                leanh::lean_ctor_set(v___x_3333_, 1, v___x_3332_);
                v___x_3334_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3334_, 0, v___x_3333_);
                leanh::lean_ctor_set(v___x_3334_, 1, v_a_3323_);
                if v_isShared_3326_ == 0 {
                    leanh::lean_ctor_set(v___x_3325_, 0, v___x_3334_);
                    v___x_3336_ = v___x_3325_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3337_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3334_);
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
                v___x_3351_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3351_, 0, v___x_3350_);
                v___x_3352_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3352_, 0, v___x_3349_);
                leanh::lean_ctor_set(v___x_3352_, 1, v___x_3351_);
                v___x_3353_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11;
                v___x_3354_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3354_, 0, v___x_3352_);
                leanh::lean_ctor_set(v___x_3354_, 1, v___x_3353_);
                v___x_3355_ = l_Nat_reprFast(v_offset_3342_);
                v___x_3356_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3356_, 0, v___x_3355_);
                v___x_3357_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3357_, 0, v___x_3354_);
                leanh::lean_ctor_set(v___x_3357_, 1, v___x_3356_);
                v___x_3358_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5;
                v___x_3359_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3359_, 0, v___x_3357_);
                leanh::lean_ctor_set(v___x_3359_, 1, v___x_3358_);
                v___x_3360_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3360_, 0, v___x_3359_);
                leanh::lean_ctor_set(v___x_3360_, 1, v_a_3345_);
                if v_isShared_3348_ == 0 {
                    leanh::lean_ctor_set(v___x_3347_, 0, v___x_3360_);
                    v___x_3362_ = v___x_3347_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3363_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
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
                leanh::lean_dec_ref(v_args_3366_);
                if leanh::lean_obj_tag(v___x_3370_) == 0 {
                    v_a_3371_ = leanh::lean_ctor_get(v___x_3370_, 0);
                    v_isSharedCheck_3384_ = (!leanh::lean_is_exclusive(v___x_3370_)) as u8;
                    if v_isSharedCheck_3384_ == 0 {
                        v___x_3373_ = v___x_3370_;
                        v_isShared_3374_ = v_isSharedCheck_3384_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3371_);
                        leanh::lean_dec(v___x_3370_);
                        v___x_3373_ = leanh::lean_box(0);
                        v_isShared_3374_ = v_isSharedCheck_3384_;
                        state = 24;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3368_);
                    leanh::lean_dec(v_fn_3365_);
                    return v___x_3370_;
                }
            }
            24 => {
                v___x_3375_ = 1;
                v___x_3376_ = l_Lean_Name_toString(v_fn_3365_, v___x_3375_);
                v___x_3377_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3377_, 0, v___x_3376_);
                if v_isShared_3369_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3368_, 5);
                    leanh::lean_ctor_set(v___x_3368_, 1, v_a_3371_);
                    leanh::lean_ctor_set(v___x_3368_, 0, v___x_3377_);
                    v___x_3379_ = v___x_3368_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3377_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_a_3371_);
                    v___x_3379_ = v_reuseFailAlloc_3383_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_3374_ == 0 {
                    leanh::lean_ctor_set(v___x_3373_, 0, v___x_3379_);
                    v___x_3381_ = v___x_3373_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
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
                leanh::lean_dec_ref(v_args_3387_);
                if leanh::lean_obj_tag(v___x_3391_) == 0 {
                    v_a_3392_ = leanh::lean_ctor_get(v___x_3391_, 0);
                    v_isSharedCheck_3407_ = (!leanh::lean_is_exclusive(v___x_3391_)) as u8;
                    if v_isSharedCheck_3407_ == 0 {
                        v___x_3394_ = v___x_3391_;
                        v_isShared_3395_ = v_isSharedCheck_3407_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3392_);
                        leanh::lean_dec(v___x_3391_);
                        v___x_3394_ = leanh::lean_box(0);
                        v_isShared_3395_ = v_isSharedCheck_3407_;
                        state = 28;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3389_);
                    leanh::lean_dec(v_fn_3386_);
                    return v___x_3391_;
                }
            }
            28 => {
                v___x_3396_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13;
                v___x_3397_ = 1;
                v___x_3398_ = l_Lean_Name_toString(v_fn_3386_, v___x_3397_);
                v___x_3399_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3399_, 0, v___x_3398_);
                if v_isShared_3390_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3389_, 5);
                    leanh::lean_ctor_set(v___x_3389_, 1, v___x_3399_);
                    leanh::lean_ctor_set(v___x_3389_, 0, v___x_3396_);
                    v___x_3401_ = v___x_3389_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3406_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3406_, 1, v___x_3399_);
                    v___x_3401_ = v_reuseFailAlloc_3406_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_3402_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3402_, 0, v___x_3401_);
                leanh::lean_ctor_set(v___x_3402_, 1, v_a_3392_);
                if v_isShared_3395_ == 0 {
                    leanh::lean_ctor_set(v___x_3394_, 0, v___x_3402_);
                    v___x_3404_ = v___x_3394_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
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
                if leanh::lean_obj_tag(v___x_3414_) == 0 {
                    v_a_3415_ = leanh::lean_ctor_get(v___x_3414_, 0);
                    v_isSharedCheck_3431_ = (!leanh::lean_is_exclusive(v___x_3414_)) as u8;
                    if v_isSharedCheck_3431_ == 0 {
                        v___x_3417_ = v___x_3414_;
                        v_isShared_3418_ = v_isSharedCheck_3431_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3415_);
                        leanh::lean_dec(v___x_3414_);
                        v___x_3417_ = leanh::lean_box(0);
                        v_isShared_3418_ = v_isSharedCheck_3431_;
                        state = 32;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3412_);
                    leanh::lean_dec(v_n_3409_);
                    return v___x_3414_;
                }
            }
            32 => {
                v___x_3419_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__15;
                v___x_3420_ = l_Nat_reprFast(v_n_3409_);
                v___x_3421_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3421_, 0, v___x_3420_);
                if v_isShared_3413_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3412_, 5);
                    leanh::lean_ctor_set(v___x_3412_, 1, v___x_3421_);
                    leanh::lean_ctor_set(v___x_3412_, 0, v___x_3419_);
                    v___x_3423_ = v___x_3412_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3430_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3421_);
                    v___x_3423_ = v_reuseFailAlloc_3430_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_3424_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5;
                v___x_3425_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3425_, 0, v___x_3423_);
                leanh::lean_ctor_set(v___x_3425_, 1, v___x_3424_);
                v___x_3426_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3426_, 0, v___x_3425_);
                leanh::lean_ctor_set(v___x_3426_, 1, v_a_3415_);
                if v_isShared_3418_ == 0 {
                    leanh::lean_ctor_set(v___x_3417_, 0, v___x_3426_);
                    v___x_3428_ = v___x_3417_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3429_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
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
                leanh::lean_inc(v___y_3446_);
                v___x_3447_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3447_, 0, v___x_3444_);
                leanh::lean_ctor_set(v___x_3447_, 1, v___y_3446_);
                v___x_3448_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_3449_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3449_, 0, v___x_3448_);
                leanh::lean_ctor_set(v___x_3449_, 1, v_a_3438_);
                v___x_3450_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__19;
                v___x_3451_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3451_, 0, v___x_3449_);
                leanh::lean_ctor_set(v___x_3451_, 1, v___x_3450_);
                v___x_3452_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(v_i_3434_);
                v___x_3453_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3453_, 0, v___x_3451_);
                leanh::lean_ctor_set(v___x_3453_, 1, v___x_3452_);
                v___x_3454_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3454_, 0, v___x_3453_);
                leanh::lean_ctor_set(v___x_3454_, 1, v_a_3440_);
                v___x_3455_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3455_, 0, v___x_3447_);
                leanh::lean_ctor_set(v___x_3455_, 1, v___x_3454_);
                if v_isShared_3443_ == 0 {
                    leanh::lean_ctor_set(v___x_3442_, 0, v___x_3455_);
                    v___x_3457_ = v___x_3442_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
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
                if leanh::lean_obj_tag(v___x_3466_) == 0 {
                    v_a_3467_ = leanh::lean_ctor_get(v___x_3466_, 0);
                    v_isSharedCheck_3478_ = (!leanh::lean_is_exclusive(v___x_3466_)) as u8;
                    if v_isSharedCheck_3478_ == 0 {
                        v___x_3469_ = v___x_3466_;
                        v_isShared_3470_ = v_isSharedCheck_3478_;
                        state = 39;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3467_);
                        leanh::lean_dec(v___x_3466_);
                        v___x_3469_ = leanh::lean_box(0);
                        v_isShared_3470_ = v_isSharedCheck_3478_;
                        state = 39;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3464_);
                    return v___x_3466_;
                }
            }
            39 => {
                v___x_3471_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__25;
                if v_isShared_3465_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3464_, 5);
                    leanh::lean_ctor_set(v___x_3464_, 1, v_a_3467_);
                    leanh::lean_ctor_set(v___x_3464_, 0, v___x_3471_);
                    v___x_3473_ = v___x_3464_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_a_3467_);
                    v___x_3473_ = v_reuseFailAlloc_3477_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3470_ == 0 {
                    leanh::lean_ctor_set(v___x_3469_, 0, v___x_3473_);
                    v___x_3475_ = v___x_3469_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
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
                v___x_3488_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3488_, 0, v___x_3487_);
                leanh::lean_ctor_set(v___x_3488_, 1, v_a_3483_);
                if v_isShared_3486_ == 0 {
                    leanh::lean_ctor_set(v___x_3485_, 0, v___x_3488_);
                    v___x_3490_ = v___x_3485_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
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
                v___x_3500_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3500_, 0, v___x_3499_);
                leanh::lean_ctor_set(v___x_3500_, 1, v_a_3495_);
                if v_isShared_3498_ == 0 {
                    leanh::lean_ctor_set(v___x_3497_, 0, v___x_3500_);
                    v___x_3502_ = v___x_3497_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3503_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
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
    mut v_pu_3505_: *mut leanh::LeanObject,
    mut v_e_3506_: *mut leanh::LeanObject,
    mut v_a_3507_: *mut leanh::LeanObject,
    mut v_a_3508_: *mut leanh::LeanObject,
    mut v_a_3509_: *mut leanh::LeanObject,
    mut v_a_3510_: *mut leanh::LeanObject,
    mut v_a_3511_: *mut leanh::LeanObject,
    mut v_a_3512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_3513_: u8 = 0;
    let mut v_res_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3513_ = (leanh::lean_unbox(v_pu_3505_) as u8);
    v_res_3514_ = l_Lean_Compiler_LCNF_PP_ppLetValue(
        v_pu_boxed_3513_,
        v_e_3506_,
        v_a_3507_,
        v_a_3508_,
        v_a_3509_,
        v_a_3510_,
        v_a_3511_,
    );
    leanh::lean_dec(v_a_3511_);
    leanh::lean_dec_ref(v_a_3510_);
    leanh::lean_dec(v_a_3509_);
    leanh::lean_dec_ref(v_a_3508_);
    leanh::lean_dec_ref(v_a_3507_);
    return v_res_3514_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParam___redArg(
    mut v_param_3519_: *mut leanh::LeanObject,
    mut v_a_3520_: *mut leanh::LeanObject,
    mut v_a_3521_: *mut leanh::LeanObject,
    mut v_a_3522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderName_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_3526_: u8 = 0;
    let mut v___y_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: u8 = 0;
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_binderName_3524_ = leanh::lean_ctor_get(v_param_3519_, 1);
                leanh::lean_inc(v_binderName_3524_);
                v_type_3525_ = leanh::lean_ctor_get(v_param_3519_, 2);
                leanh::lean_inc_ref(v_type_3525_);
                v_borrow_3526_ = leanh::lean_ctor_get_uint8(
                    v_param_3519_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_param_3519_);
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
                v_options_3529_ = leanh::lean_ctor_get(v_a_3521_, 2);
                v___x_3530_ = l_Lean_pp_funBinderTypes;
                v___x_3531_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                    v_options_3529_,
                    v___x_3530_,
                );
                if v___x_3531_ == 0 {
                    leanh::lean_dec_ref(v_type_3525_);
                    v___x_3532_ = 1;
                    v___x_3533_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_binderName_3524_,
                        v___x_3532_,
                    );
                    leanh::lean_inc_ref(v___y_3528_);
                    v___x_3534_ = lean_string_append(v___y_3528_, v___x_3533_);
                    leanh::lean_dec_ref(v___x_3533_);
                    v___x_3535_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3535_, 0, v___x_3534_);
                    v___x_3536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3536_, 0, v___x_3535_);
                    return v___x_3536_;
                } else {
                    v___x_3537_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                        v_type_3525_,
                        v_a_3520_,
                        v_a_3521_,
                        v_a_3522_,
                    );
                    if leanh::lean_obj_tag(v___x_3537_) == 0 {
                        v_a_3538_ = leanh::lean_ctor_get(v___x_3537_, 0);
                        v_isSharedCheck_3560_ =
                            (!leanh::lean_is_exclusive(v___x_3537_)) as u8;
                        if v_isSharedCheck_3560_ == 0 {
                            v___x_3540_ = v___x_3537_;
                            v_isShared_3541_ = v_isSharedCheck_3560_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3538_);
                            leanh::lean_dec(v___x_3537_);
                            v___x_3540_ = leanh::lean_box(0);
                            v_isShared_3541_ = v_isSharedCheck_3560_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_binderName_3524_);
                        return v___x_3537_;
                    }
                }
            }
            2 => {
                v___x_3542_ = l_Lean_Name_toString(v_binderName_3524_, v___x_3531_);
                v___x_3543_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3543_, 0, v___x_3542_);
                v___x_3544_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_3545_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3545_, 0, v___x_3543_);
                leanh::lean_ctor_set(v___x_3545_, 1, v___x_3544_);
                leanh::lean_inc_ref(v___y_3528_);
                v___x_3546_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3546_, 0, v___y_3528_);
                v___x_3547_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3547_, 0, v___x_3545_);
                leanh::lean_ctor_set(v___x_3547_, 1, v___x_3546_);
                v___x_3548_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3548_, 0, v___x_3547_);
                leanh::lean_ctor_set(v___x_3548_, 1, v_a_3538_);
                v___x_3549_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7_once
                    ),
                    _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7,
                );
                v___x_3550_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8;
                v___x_3551_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3551_, 0, v___x_3550_);
                leanh::lean_ctor_set(v___x_3551_, 1, v___x_3548_);
                v___x_3552_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9;
                v___x_3553_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3553_, 0, v___x_3551_);
                leanh::lean_ctor_set(v___x_3553_, 1, v___x_3552_);
                v___x_3554_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3554_, 0, v___x_3549_);
                leanh::lean_ctor_set(v___x_3554_, 1, v___x_3553_);
                v___x_3555_ = 0;
                v___x_3556_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3556_, 0, v___x_3554_);
                leanh::lean_ctor_set_uint8(
                    v___x_3556_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3555_,
                );
                if v_isShared_3541_ == 0 {
                    leanh::lean_ctor_set(v___x_3540_, 0, v___x_3556_);
                    v___x_3558_ = v___x_3540_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3559_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
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
    mut v_param_3563_: *mut leanh::LeanObject,
    mut v_a_3564_: *mut leanh::LeanObject,
    mut v_a_3565_: *mut leanh::LeanObject,
    mut v_a_3566_: *mut leanh::LeanObject,
    mut v_a_3567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3568_ =
        l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
    leanh::lean_dec(v_a_3566_);
    leanh::lean_dec_ref(v_a_3565_);
    leanh::lean_dec_ref(v_a_3564_);
    return v_res_3568_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParam(
    mut v_pu_3569_: u8,
    mut v_param_3570_: *mut leanh::LeanObject,
    mut v_a_3571_: *mut leanh::LeanObject,
    mut v_a_3572_: *mut leanh::LeanObject,
    mut v_a_3573_: *mut leanh::LeanObject,
    mut v_a_3574_: *mut leanh::LeanObject,
    mut v_a_3575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3577_ =
        l_Lean_Compiler_LCNF_PP_ppParam___redArg(v_param_3570_, v_a_3571_, v_a_3574_, v_a_3575_);
    return v___x_3577_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParam___boxed(
    mut v_pu_3578_: *mut leanh::LeanObject,
    mut v_param_3579_: *mut leanh::LeanObject,
    mut v_a_3580_: *mut leanh::LeanObject,
    mut v_a_3581_: *mut leanh::LeanObject,
    mut v_a_3582_: *mut leanh::LeanObject,
    mut v_a_3583_: *mut leanh::LeanObject,
    mut v_a_3584_: *mut leanh::LeanObject,
    mut v_a_3585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_3586_: u8 = 0;
    let mut v_res_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3586_ = (leanh::lean_unbox(v_pu_3578_) as u8);
    v_res_3587_ = l_Lean_Compiler_LCNF_PP_ppParam(
        v_pu_boxed_3586_,
        v_param_3579_,
        v_a_3580_,
        v_a_3581_,
        v_a_3582_,
        v_a_3583_,
        v_a_3584_,
    );
    leanh::lean_dec(v_a_3584_);
    leanh::lean_dec_ref(v_a_3583_);
    leanh::lean_dec(v_a_3582_);
    leanh::lean_dec_ref(v_a_3581_);
    leanh::lean_dec_ref(v_a_3580_);
    return v_res_3587_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppParams(
    mut v_pu_3588_: u8,
    mut v_params_3589_: *mut leanh::LeanObject,
    mut v_a_3590_: *mut leanh::LeanObject,
    mut v_a_3591_: *mut leanh::LeanObject,
    mut v_a_3592_: *mut leanh::LeanObject,
    mut v_a_3593_: *mut leanh::LeanObject,
    mut v_a_3594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3596_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
    v___x_3597_ = leanh::lean_box((v_pu_3588_) as usize);
    v___x_3598_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PP_ppParam___boxed as *mut core::ffi::c_void,
        8,
        1,
    );
    leanh::lean_closure_set(v___x_3598_, 0, v___x_3597_);
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
    mut v_pu_3600_: *mut leanh::LeanObject,
    mut v_params_3601_: *mut leanh::LeanObject,
    mut v_a_3602_: *mut leanh::LeanObject,
    mut v_a_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
    mut v_a_3605_: *mut leanh::LeanObject,
    mut v_a_3606_: *mut leanh::LeanObject,
    mut v_a_3607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_3608_: u8 = 0;
    let mut v_res_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3608_ = (leanh::lean_unbox(v_pu_3600_) as u8);
    v_res_3609_ = l_Lean_Compiler_LCNF_PP_ppParams(
        v_pu_boxed_3608_,
        v_params_3601_,
        v_a_3602_,
        v_a_3603_,
        v_a_3604_,
        v_a_3605_,
        v_a_3606_,
    );
    leanh::lean_dec(v_a_3606_);
    leanh::lean_dec_ref(v_a_3605_);
    leanh::lean_dec(v_a_3604_);
    leanh::lean_dec_ref(v_a_3603_);
    leanh::lean_dec_ref(v_a_3602_);
    leanh::lean_dec_ref(v_params_3601_);
    return v_res_3609_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppLetDecl(
    mut v_pu_3616_: u8,
    mut v_letDecl_3617_: *mut leanh::LeanObject,
    mut v_a_3618_: *mut leanh::LeanObject,
    mut v_a_3619_: *mut leanh::LeanObject,
    mut v_a_3620_: *mut leanh::LeanObject,
    mut v_a_3621_: *mut leanh::LeanObject,
    mut v_a_3622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: u8 = 0;
    let mut v_binderName_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3633_: u8 = 0;
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: u8 = 0;
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut v_binderName_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3624_ = leanh::lean_ctor_get(v_a_3621_, 2);
                v___x_3625_ = l_Lean_pp_letVarTypes;
                v___x_3626_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                    v_options_3624_,
                    v___x_3625_,
                );
                if v___x_3626_ == 0 {
                    v_binderName_3627_ = leanh::lean_ctor_get(v_letDecl_3617_, 1);
                    leanh::lean_inc(v_binderName_3627_);
                    v_value_3628_ = leanh::lean_ctor_get(v_letDecl_3617_, 3);
                    leanh::lean_inc(v_value_3628_);
                    leanh::lean_dec_ref(v_letDecl_3617_);
                    v___x_3629_ = l_Lean_Compiler_LCNF_PP_ppLetValue(
                        v_pu_3616_,
                        v_value_3628_,
                        v_a_3618_,
                        v_a_3619_,
                        v_a_3620_,
                        v_a_3621_,
                        v_a_3622_,
                    );
                    if leanh::lean_obj_tag(v___x_3629_) == 0 {
                        v_a_3630_ = leanh::lean_ctor_get(v___x_3629_, 0);
                        v_isSharedCheck_3645_ =
                            (!leanh::lean_is_exclusive(v___x_3629_)) as u8;
                        if v_isSharedCheck_3645_ == 0 {
                            v___x_3632_ = v___x_3629_;
                            v_isShared_3633_ = v_isSharedCheck_3645_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3630_);
                            leanh::lean_dec(v___x_3629_);
                            v___x_3632_ = leanh::lean_box(0);
                            v_isShared_3633_ = v_isSharedCheck_3645_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_binderName_3627_);
                        return v___x_3629_;
                    }
                } else {
                    v_binderName_3646_ = leanh::lean_ctor_get(v_letDecl_3617_, 1);
                    leanh::lean_inc(v_binderName_3646_);
                    v_type_3647_ = leanh::lean_ctor_get(v_letDecl_3617_, 2);
                    leanh::lean_inc_ref(v_type_3647_);
                    v_value_3648_ = leanh::lean_ctor_get(v_letDecl_3617_, 3);
                    leanh::lean_inc(v_value_3648_);
                    leanh::lean_dec_ref(v_letDecl_3617_);
                    v___x_3649_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                        v_type_3647_,
                        v_a_3618_,
                        v_a_3621_,
                        v_a_3622_,
                    );
                    if leanh::lean_obj_tag(v___x_3649_) == 0 {
                        v_a_3650_ = leanh::lean_ctor_get(v___x_3649_, 0);
                        v_isSharedCheck_3675_ =
                            (!leanh::lean_is_exclusive(v___x_3649_)) as u8;
                        if v_isSharedCheck_3675_ == 0 {
                            v___x_3652_ = v___x_3649_;
                            v_isShared_3653_ = v_isSharedCheck_3675_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3650_);
                            leanh::lean_dec(v___x_3649_);
                            v___x_3652_ = leanh::lean_box(0);
                            v_isShared_3653_ = v_isSharedCheck_3675_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_value_3648_);
                        leanh::lean_dec(v_binderName_3646_);
                        return v___x_3649_;
                    }
                }
            }
            1 => {
                v___x_3634_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1;
                v___x_3635_ = 1;
                v___x_3636_ = l_Lean_Name_toString(v_binderName_3627_, v___x_3635_);
                v___x_3637_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3637_, 0, v___x_3636_);
                v___x_3638_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3638_, 0, v___x_3634_);
                leanh::lean_ctor_set(v___x_3638_, 1, v___x_3637_);
                v___x_3639_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
                v___x_3640_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3640_, 0, v___x_3638_);
                leanh::lean_ctor_set(v___x_3640_, 1, v___x_3639_);
                v___x_3641_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3641_, 0, v___x_3640_);
                leanh::lean_ctor_set(v___x_3641_, 1, v_a_3630_);
                if v_isShared_3633_ == 0 {
                    leanh::lean_ctor_set(v___x_3632_, 0, v___x_3641_);
                    v___x_3643_ = v___x_3632_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
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
                if leanh::lean_obj_tag(v___x_3654_) == 0 {
                    v_a_3655_ = leanh::lean_ctor_get(v___x_3654_, 0);
                    v_isSharedCheck_3674_ = (!leanh::lean_is_exclusive(v___x_3654_)) as u8;
                    if v_isSharedCheck_3674_ == 0 {
                        v___x_3657_ = v___x_3654_;
                        v_isShared_3658_ = v_isSharedCheck_3674_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3655_);
                        leanh::lean_dec(v___x_3654_);
                        v___x_3657_ = leanh::lean_box(0);
                        v_isShared_3658_ = v_isSharedCheck_3674_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3652_);
                    leanh::lean_dec(v_a_3650_);
                    leanh::lean_dec(v_binderName_3646_);
                    return v___x_3654_;
                }
            }
            4 => {
                v___x_3659_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1;
                v___x_3660_ = l_Lean_Name_toString(v_binderName_3646_, v___x_3626_);
                if v_isShared_3653_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3652_, 3);
                    leanh::lean_ctor_set(v___x_3652_, 0, v___x_3660_);
                    v___x_3662_ = v___x_3652_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3660_);
                    v___x_3662_ = v_reuseFailAlloc_3673_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3663_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3663_, 0, v___x_3659_);
                leanh::lean_ctor_set(v___x_3663_, 1, v___x_3662_);
                v___x_3664_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_3665_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3665_, 0, v___x_3663_);
                leanh::lean_ctor_set(v___x_3665_, 1, v___x_3664_);
                v___x_3666_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3666_, 0, v___x_3665_);
                leanh::lean_ctor_set(v___x_3666_, 1, v_a_3650_);
                v___x_3667_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
                v___x_3668_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3668_, 0, v___x_3666_);
                leanh::lean_ctor_set(v___x_3668_, 1, v___x_3667_);
                v___x_3669_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3669_, 0, v___x_3668_);
                leanh::lean_ctor_set(v___x_3669_, 1, v_a_3655_);
                if v_isShared_3658_ == 0 {
                    leanh::lean_ctor_set(v___x_3657_, 0, v___x_3669_);
                    v___x_3671_ = v___x_3657_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
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
    mut v_pu_3676_: *mut leanh::LeanObject,
    mut v_letDecl_3677_: *mut leanh::LeanObject,
    mut v_a_3678_: *mut leanh::LeanObject,
    mut v_a_3679_: *mut leanh::LeanObject,
    mut v_a_3680_: *mut leanh::LeanObject,
    mut v_a_3681_: *mut leanh::LeanObject,
    mut v_a_3682_: *mut leanh::LeanObject,
    mut v_a_3683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_3684_: u8 = 0;
    let mut v_res_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3684_ = (leanh::lean_unbox(v_pu_3676_) as u8);
    v_res_3685_ = l_Lean_Compiler_LCNF_PP_ppLetDecl(
        v_pu_boxed_3684_,
        v_letDecl_3677_,
        v_a_3678_,
        v_a_3679_,
        v_a_3680_,
        v_a_3681_,
        v_a_3682_,
    );
    leanh::lean_dec(v_a_3682_);
    leanh::lean_dec_ref(v_a_3681_);
    leanh::lean_dec(v_a_3680_);
    leanh::lean_dec_ref(v_a_3679_);
    leanh::lean_dec_ref(v_a_3678_);
    return v_res_3685_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(
    mut v_sz_3686_: usize,
    mut v_i_3687_: usize,
    mut v_bs_3688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3689_: u8 = 0;
    let mut v_v_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: usize = 0;
    let mut v___x_3696_: usize = 0;
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3689_ = lean_usize_dec_lt(v_i_3687_, v_sz_3686_);
                if v___x_3689_ == 0 {
                    return v_bs_3688_;
                } else {
                    v_v_3690_ = lean_array_uget_borrowed(v_bs_3688_, v_i_3687_);
                    v_fvarId_3691_ = leanh::lean_ctor_get(v_v_3690_, 0);
                    leanh::lean_inc(v_fvarId_3691_);
                    v___x_3692_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_3699_: *mut leanh::LeanObject,
    mut v_i_3700_: *mut leanh::LeanObject,
    mut v_bs_3701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3702_: usize = 0;
    let mut v_i_boxed_3703_: usize = 0;
    let mut v_res_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3702_ = leanh::lean_unbox_usize(v_sz_3699_);
    leanh::lean_dec(v_sz_3699_);
    v_i_boxed_3703_ = leanh::lean_unbox_usize(v_i_3700_);
    leanh::lean_dec(v_i_3700_);
    v_res_3704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_boxed_3702_, v_i_boxed_3703_, v_bs_3701_);
    return v_res_3704_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_getFunType(
    mut v_pu_3705_: u8,
    mut v_ps_3706_: *mut leanh::LeanObject,
    mut v_type_3707_: *mut leanh::LeanObject,
    mut v_a_3708_: *mut leanh::LeanObject,
    mut v_a_3709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3711_: u8 = 0;
    v___x_3711_ = l_Lean_Expr_isErased(v_type_3707_);
    if v___x_3711_ == 0 {
        if v_pu_3705_ == 0 {
            let mut v_sz_3712_: usize = 0;
            let mut v___x_3713_: usize = 0;
            let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_sz_3712_ = lean_array_size(v_ps_3706_);
            v___x_3713_ = 0usize;
            v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(v_sz_3712_, v___x_3713_, v_ps_3706_);
            v___x_3715_ = l_Lean_Compiler_LCNF_instantiateForall(
                v_type_3707_,
                v___x_3714_,
                v_a_3708_,
                v_a_3709_,
            );
            leanh::lean_dec_ref(v___x_3714_);
            return v___x_3715_;
        } else {
            let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_ps_3706_);
            v___x_3716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3716_, 0, v_type_3707_);
            return v___x_3716_;
        }
    } else {
        let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ps_3706_);
        v___x_3717_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3717_, 0, v_type_3707_);
        return v___x_3717_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_getFunType___boxed(
    mut v_pu_3718_: *mut leanh::LeanObject,
    mut v_ps_3719_: *mut leanh::LeanObject,
    mut v_type_3720_: *mut leanh::LeanObject,
    mut v_a_3721_: *mut leanh::LeanObject,
    mut v_a_3722_: *mut leanh::LeanObject,
    mut v_a_3723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_3724_: u8 = 0;
    let mut v_res_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3724_ = (leanh::lean_unbox(v_pu_3718_) as u8);
    v_res_3725_ = l_Lean_Compiler_LCNF_PP_getFunType(
        v_pu_boxed_3724_,
        v_ps_3719_,
        v_type_3720_,
        v_a_3721_,
        v_a_3722_,
    );
    leanh::lean_dec(v_a_3722_);
    leanh::lean_dec_ref(v_a_3721_);
    return v_res_3725_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppAlt(
    mut v_pu_3750_: u8,
    mut v_alt_3751_: *mut leanh::LeanObject,
    mut v_a_3752_: *mut leanh::LeanObject,
    mut v_a_3753_: *mut leanh::LeanObject,
    mut v_a_3754_: *mut leanh::LeanObject,
    mut v_a_3755_: *mut leanh::LeanObject,
    mut v_a_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ctorName_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3770_: u8 = 0;
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: u8 = 0;
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3786_: u8 = 0;
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_info_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3792_: u8 = 0;
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v_name_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3813_: u8 = 0;
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v_code_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3820_: u8 = 0;
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_alt_3751_) {
                0 => {
                    v_ctorName_3758_ = leanh::lean_ctor_get(v_alt_3751_, 0);
                    leanh::lean_inc(v_ctorName_3758_);
                    v_params_3759_ = leanh::lean_ctor_get(v_alt_3751_, 1);
                    leanh::lean_inc_ref(v_params_3759_);
                    v_code_3760_ = leanh::lean_ctor_get(v_alt_3751_, 2);
                    leanh::lean_inc_ref(v_code_3760_);
                    leanh::lean_dec_ref_known(v_alt_3751_, 3);
                    v___x_3761_ = l_Lean_Compiler_LCNF_PP_ppParams(
                        v_pu_3750_,
                        v_params_3759_,
                        v_a_3752_,
                        v_a_3753_,
                        v_a_3754_,
                        v_a_3755_,
                        v_a_3756_,
                    );
                    leanh::lean_dec_ref(v_params_3759_);
                    if leanh::lean_obj_tag(v___x_3761_) == 0 {
                        v_a_3762_ = leanh::lean_ctor_get(v___x_3761_, 0);
                        v_isSharedCheck_3787_ =
                            (!leanh::lean_is_exclusive(v___x_3761_)) as u8;
                        if v_isSharedCheck_3787_ == 0 {
                            v___x_3764_ = v___x_3761_;
                            v_isShared_3765_ = v_isSharedCheck_3787_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3762_);
                            leanh::lean_dec(v___x_3761_);
                            v___x_3764_ = leanh::lean_box(0);
                            v_isShared_3765_ = v_isSharedCheck_3787_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_code_3760_);
                        leanh::lean_dec(v_ctorName_3758_);
                        return v___x_3761_;
                    }
                }
                1 => {
                    v_info_3788_ = leanh::lean_ctor_get(v_alt_3751_, 0);
                    v_code_3789_ = leanh::lean_ctor_get(v_alt_3751_, 1);
                    v_isSharedCheck_3814_ = (!leanh::lean_is_exclusive(v_alt_3751_)) as u8;
                    if v_isSharedCheck_3814_ == 0 {
                        v___x_3791_ = v_alt_3751_;
                        v_isShared_3792_ = v_isSharedCheck_3814_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_code_3789_);
                        leanh::lean_inc(v_info_3788_);
                        leanh::lean_dec(v_alt_3751_);
                        v___x_3791_ = leanh::lean_box(0);
                        v_isShared_3792_ = v_isSharedCheck_3814_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_code_3815_ = leanh::lean_ctor_get(v_alt_3751_, 0);
                    leanh::lean_inc_ref(v_code_3815_);
                    leanh::lean_dec_ref_known(v_alt_3751_, 1);
                    v___x_3816_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3750_,
                        v_code_3815_,
                        v_a_3752_,
                        v_a_3753_,
                        v_a_3754_,
                        v_a_3755_,
                        v_a_3756_,
                    );
                    if leanh::lean_obj_tag(v___x_3816_) == 0 {
                        v_a_3817_ = leanh::lean_ctor_get(v___x_3816_, 0);
                        v_isSharedCheck_3827_ =
                            (!leanh::lean_is_exclusive(v___x_3816_)) as u8;
                        if v_isSharedCheck_3827_ == 0 {
                            v___x_3819_ = v___x_3816_;
                            v_isShared_3820_ = v_isSharedCheck_3827_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3817_);
                            leanh::lean_dec(v___x_3816_);
                            v___x_3819_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v___x_3766_) == 0 {
                    v_a_3767_ = leanh::lean_ctor_get(v___x_3766_, 0);
                    v_isSharedCheck_3786_ = (!leanh::lean_is_exclusive(v___x_3766_)) as u8;
                    if v_isSharedCheck_3786_ == 0 {
                        v___x_3769_ = v___x_3766_;
                        v_isShared_3770_ = v_isSharedCheck_3786_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3767_);
                        leanh::lean_dec(v___x_3766_);
                        v___x_3769_ = leanh::lean_box(0);
                        v_isShared_3770_ = v_isSharedCheck_3786_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3764_);
                    leanh::lean_dec(v_a_3762_);
                    leanh::lean_dec(v_ctorName_3758_);
                    return v___x_3766_;
                }
            }
            2 => {
                v___x_3771_ = l_Lean_Compiler_LCNF_PP_ppAlt___closed__1;
                v___x_3772_ = 1;
                v___x_3773_ = l_Lean_Name_toString(v_ctorName_3758_, v___x_3772_);
                if v_isShared_3765_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3764_, 3);
                    leanh::lean_ctor_set(v___x_3764_, 0, v___x_3773_);
                    v___x_3775_ = v___x_3764_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3785_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3773_);
                    v___x_3775_ = v_reuseFailAlloc_3785_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3776_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3776_, 0, v___x_3771_);
                leanh::lean_ctor_set(v___x_3776_, 1, v___x_3775_);
                v___x_3777_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3777_, 0, v___x_3776_);
                leanh::lean_ctor_set(v___x_3777_, 1, v_a_3762_);
                v___x_3778_ = l_Lean_Compiler_LCNF_PP_ppAlt___closed__3;
                v___x_3779_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3779_, 0, v___x_3777_);
                leanh::lean_ctor_set(v___x_3779_, 1, v___x_3778_);
                v___x_3780_ = l_Std_Format_indentD(v_a_3767_);
                v___x_3781_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3781_, 0, v___x_3779_);
                leanh::lean_ctor_set(v___x_3781_, 1, v___x_3780_);
                if v_isShared_3770_ == 0 {
                    leanh::lean_ctor_set(v___x_3769_, 0, v___x_3781_);
                    v___x_3783_ = v___x_3769_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3784_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
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
                if leanh::lean_obj_tag(v___x_3793_) == 0 {
                    v_a_3794_ = leanh::lean_ctor_get(v___x_3793_, 0);
                    v_isSharedCheck_3813_ = (!leanh::lean_is_exclusive(v___x_3793_)) as u8;
                    if v_isSharedCheck_3813_ == 0 {
                        v___x_3796_ = v___x_3793_;
                        v_isShared_3797_ = v_isSharedCheck_3813_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3794_);
                        leanh::lean_dec(v___x_3793_);
                        v___x_3796_ = leanh::lean_box(0);
                        v_isShared_3797_ = v_isSharedCheck_3813_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3791_);
                    leanh::lean_dec_ref(v_info_3788_);
                    return v___x_3793_;
                }
            }
            6 => {
                v_name_3798_ = leanh::lean_ctor_get(v_info_3788_, 0);
                leanh::lean_inc(v_name_3798_);
                leanh::lean_dec_ref(v_info_3788_);
                v___x_3799_ = l_Lean_Compiler_LCNF_PP_ppAlt___closed__1;
                v___x_3800_ = 1;
                v___x_3801_ = l_Lean_Name_toString(v_name_3798_, v___x_3800_);
                v___x_3802_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3802_, 0, v___x_3801_);
                if v_isShared_3792_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3791_, 5);
                    leanh::lean_ctor_set(v___x_3791_, 1, v___x_3802_);
                    leanh::lean_ctor_set(v___x_3791_, 0, v___x_3799_);
                    v___x_3804_ = v___x_3791_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3812_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 1, v___x_3802_);
                    v___x_3804_ = v_reuseFailAlloc_3812_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3805_ = l_Lean_Compiler_LCNF_PP_ppAlt___closed__3;
                v___x_3806_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3806_, 0, v___x_3804_);
                leanh::lean_ctor_set(v___x_3806_, 1, v___x_3805_);
                v___x_3807_ = l_Std_Format_indentD(v_a_3794_);
                v___x_3808_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3808_, 0, v___x_3806_);
                leanh::lean_ctor_set(v___x_3808_, 1, v___x_3807_);
                if v_isShared_3797_ == 0 {
                    leanh::lean_ctor_set(v___x_3796_, 0, v___x_3808_);
                    v___x_3810_ = v___x_3796_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3811_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
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
                v___x_3823_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3823_, 0, v___x_3821_);
                leanh::lean_ctor_set(v___x_3823_, 1, v___x_3822_);
                if v_isShared_3820_ == 0 {
                    leanh::lean_ctor_set(v___x_3819_, 0, v___x_3823_);
                    v___x_3825_ = v___x_3819_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3826_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
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
    mut v_pu_3828_: *mut leanh::LeanObject,
    mut v_alt_3829_: *mut leanh::LeanObject,
    mut v_a_3830_: *mut leanh::LeanObject,
    mut v_a_3831_: *mut leanh::LeanObject,
    mut v_a_3832_: *mut leanh::LeanObject,
    mut v_a_3833_: *mut leanh::LeanObject,
    mut v_a_3834_: *mut leanh::LeanObject,
    mut v_a_3835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_3836_: u8 = 0;
    let mut v_res_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3836_ = (leanh::lean_unbox(v_pu_3828_) as u8);
    v_res_3837_ = l_Lean_Compiler_LCNF_PP_ppAlt(
        v_pu_boxed_3836_,
        v_alt_3829_,
        v_a_3830_,
        v_a_3831_,
        v_a_3832_,
        v_a_3833_,
        v_a_3834_,
    );
    leanh::lean_dec(v_a_3834_);
    leanh::lean_dec_ref(v_a_3833_);
    leanh::lean_dec(v_a_3832_);
    leanh::lean_dec_ref(v_a_3831_);
    leanh::lean_dec_ref(v_a_3830_);
    return v_res_3837_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppCode(
    mut v_pu_3889_: u8,
    mut v_c_3890_: *mut leanh::LeanObject,
    mut v_a_3891_: *mut leanh::LeanObject,
    mut v_a_3892_: *mut leanh::LeanObject,
    mut v_a_3893_: *mut leanh::LeanObject,
    mut v_a_3894_: *mut leanh::LeanObject,
    mut v_a_3895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3908_: u8 = 0;
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut v_isSharedCheck_3920_: u8 = 0;
    let mut v_decl_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3932_: u8 = 0;
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3945_: u8 = 0;
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v_decl_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3971_: u8 = 0;
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v_fvarId_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3977_: u8 = 0;
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3984_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3993_: u8 = 0;
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v_cases_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4010_: u8 = 0;
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v_fvarId_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4032_: u8 = 0;
    let mut v_type_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4036_: u8 = 0;
    let mut v_options_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4048_: u8 = 0;
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4054_: u8 = 0;
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut v_fvarId_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4066_: u8 = 0;
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4071_: u8 = 0;
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut v_fvarId_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4130_: u8 = 0;
    let mut v_isSharedCheck_4131_: u8 = 0;
    let mut v_fvarId_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: u8 = 0;
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4150_: u8 = 0;
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4155_: u8 = 0;
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_isSharedCheck_4184_: u8 = 0;
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4197_: u8 = 0;
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4202_: u8 = 0;
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_isSharedCheck_4234_: u8 = 0;
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut v_fvarId_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4243_: u8 = 0;
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut v_isSharedCheck_4267_: u8 = 0;
    let mut v_fvarId_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_4270_: u8 = 0;
    let mut v_persistent_4271_: u8 = 0;
    let mut v_k_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: u8 = 0;
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4283_: u8 = 0;
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v_isSharedCheck_4311_: u8 = 0;
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_isSharedCheck_4339_: u8 = 0;
    let mut v___y_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_check_4348_: u8 = 0;
    let mut v_persistent_4349_: u8 = 0;
    let mut v_objs_x3f_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4365_: u8 = 0;
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4370_: u8 = 0;
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut v_isSharedCheck_4393_: u8 = 0;
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4420_: u8 = 0;
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut v_ann_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ann_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4471_: u8 = 0;
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_c_3890_) {
                0 => {
                    v_decl_3897_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    v_k_3898_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_3920_ = (!leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_3920_ == 0 {
                        v___x_3900_ = v_c_3890_;
                        v_isShared_3901_ = v_isSharedCheck_3920_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_3898_);
                        leanh::lean_inc(v_decl_3897_);
                        leanh::lean_dec(v_c_3890_);
                        v___x_3900_ = leanh::lean_box(0);
                        v_isShared_3901_ = v_isSharedCheck_3920_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_decl_3921_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    v_k_3922_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_3946_ = (!leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_3946_ == 0 {
                        v___x_3924_ = v_c_3890_;
                        v_isShared_3925_ = v_isSharedCheck_3946_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_3922_);
                        leanh::lean_inc(v_decl_3921_);
                        leanh::lean_dec(v_c_3890_);
                        v___x_3924_ = leanh::lean_box(0);
                        v_isShared_3925_ = v_isSharedCheck_3946_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_decl_3947_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    v_k_3948_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_3972_ = (!leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_3972_ == 0 {
                        v___x_3950_ = v_c_3890_;
                        v_isShared_3951_ = v_isSharedCheck_3972_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_3948_);
                        leanh::lean_inc(v_decl_3947_);
                        leanh::lean_dec(v_c_3890_);
                        v___x_3950_ = leanh::lean_box(0);
                        v_isShared_3951_ = v_isSharedCheck_3972_;
                        state = 9;
                        continue;
                    }
                }
                3 => {
                    v_fvarId_3973_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    v_args_3974_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_3994_ = (!leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_3994_ == 0 {
                        v___x_3976_ = v_c_3890_;
                        v_isShared_3977_ = v_isSharedCheck_3994_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_args_3974_);
                        leanh::lean_inc(v_fvarId_3973_);
                        leanh::lean_dec(v_c_3890_);
                        v___x_3976_ = leanh::lean_box(0);
                        v_isShared_3977_ = v_isSharedCheck_3994_;
                        state = 13;
                        continue;
                    }
                }
                4 => {
                    v_cases_3995_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    leanh::lean_inc_ref(v_cases_3995_);
                    leanh::lean_dec_ref_known(v_c_3890_, 1);
                    v_resultType_3996_ = leanh::lean_ctor_get(v_cases_3995_, 1);
                    leanh::lean_inc_ref(v_resultType_3996_);
                    v_discr_3997_ = leanh::lean_ctor_get(v_cases_3995_, 2);
                    leanh::lean_inc(v_discr_3997_);
                    v_alts_3998_ = leanh::lean_ctor_get(v_cases_3995_, 3);
                    leanh::lean_inc_ref(v_alts_3998_);
                    leanh::lean_dec_ref(v_cases_3995_);
                    v___x_3999_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_discr_3997_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_3999_) == 0 {
                        v_a_4000_ = leanh::lean_ctor_get(v___x_3999_, 0);
                        leanh::lean_inc(v_a_4000_);
                        leanh::lean_dec_ref_known(v___x_3999_, 1);
                        v___x_4001_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                            v_resultType_3996_,
                            v_a_3891_,
                            v_a_3894_,
                            v_a_3895_,
                        );
                        if leanh::lean_obj_tag(v___x_4001_) == 0 {
                            v_a_4002_ = leanh::lean_ctor_get(v___x_4001_, 0);
                            leanh::lean_inc(v_a_4002_);
                            leanh::lean_dec_ref_known(v___x_4001_, 1);
                            v___x_4003_ = leanh::lean_box(1);
                            v___x_4004_ = leanh::lean_box((v_pu_3889_) as usize);
                            v___x_4005_ = leanh::lean_alloc_closure(
                                l_Lean_Compiler_LCNF_PP_ppAlt___boxed as *mut core::ffi::c_void,
                                8,
                                1,
                            );
                            leanh::lean_closure_set(v___x_4005_, 0, v___x_4004_);
                            v___x_4006_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(v___x_4003_, v_alts_3998_, v___x_4005_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
                            leanh::lean_dec_ref(v_alts_3998_);
                            if leanh::lean_obj_tag(v___x_4006_) == 0 {
                                v_a_4007_ = leanh::lean_ctor_get(v___x_4006_, 0);
                                v_isSharedCheck_4020_ =
                                    (!leanh::lean_is_exclusive(v___x_4006_)) as u8;
                                if v_isSharedCheck_4020_ == 0 {
                                    v___x_4009_ = v___x_4006_;
                                    v_isShared_4010_ = v_isSharedCheck_4020_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4007_);
                                    leanh::lean_dec(v___x_4006_);
                                    v___x_4009_ = leanh::lean_box(0);
                                    v_isShared_4010_ = v_isSharedCheck_4020_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_4002_);
                                leanh::lean_dec(v_a_4000_);
                                return v___x_4006_;
                            }
                        } else {
                            leanh::lean_dec(v_a_4000_);
                            leanh::lean_dec_ref(v_alts_3998_);
                            return v___x_4001_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_alts_3998_);
                        leanh::lean_dec_ref(v_resultType_3996_);
                        return v___x_3999_;
                    }
                }
                5 => {
                    v_fvarId_4021_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    leanh::lean_inc(v_fvarId_4021_);
                    leanh::lean_dec_ref_known(v_c_3890_, 1);
                    v___x_4022_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4021_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_4022_) == 0 {
                        v_a_4023_ = leanh::lean_ctor_get(v___x_4022_, 0);
                        v_isSharedCheck_4032_ =
                            (!leanh::lean_is_exclusive(v___x_4022_)) as u8;
                        if v_isSharedCheck_4032_ == 0 {
                            v___x_4025_ = v___x_4022_;
                            v_isShared_4026_ = v_isSharedCheck_4032_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4023_);
                            leanh::lean_dec(v___x_4022_);
                            v___x_4025_ = leanh::lean_box(0);
                            v_isShared_4026_ = v_isSharedCheck_4032_;
                            state = 19;
                            continue;
                        }
                    } else {
                        return v___x_4022_;
                    }
                }
                6 => {
                    v_type_4033_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    v_isSharedCheck_4055_ = (!leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_4055_ == 0 {
                        v___x_4035_ = v_c_3890_;
                        v_isShared_4036_ = v_isSharedCheck_4055_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_type_4033_);
                        leanh::lean_dec(v_c_3890_);
                        v___x_4035_ = leanh::lean_box(0);
                        v_isShared_4036_ = v_isSharedCheck_4055_;
                        state = 21;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_4056_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    leanh::lean_inc(v_fvarId_4056_);
                    v_i_4057_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    leanh::lean_inc(v_i_4057_);
                    v_y_4058_ = leanh::lean_ctor_get(v_c_3890_, 2);
                    leanh::lean_inc(v_y_4058_);
                    v_k_4059_ = leanh::lean_ctor_get(v_c_3890_, 3);
                    leanh::lean_inc_ref(v_k_4059_);
                    leanh::lean_dec_ref_known(v_c_3890_, 4);
                    v___x_4060_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4056_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_4060_) == 0 {
                        v_a_4061_ = leanh::lean_ctor_get(v___x_4060_, 0);
                        leanh::lean_inc(v_a_4061_);
                        leanh::lean_dec_ref_known(v___x_4060_, 1);
                        v___x_4062_ = l_Lean_Compiler_LCNF_PP_ppArg___redArg(
                            v_y_4058_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                        );
                        if leanh::lean_obj_tag(v___x_4062_) == 0 {
                            v_a_4063_ = leanh::lean_ctor_get(v___x_4062_, 0);
                            v_isSharedCheck_4093_ =
                                (!leanh::lean_is_exclusive(v___x_4062_)) as u8;
                            if v_isSharedCheck_4093_ == 0 {
                                v___x_4065_ = v___x_4062_;
                                v_isShared_4066_ = v_isSharedCheck_4093_;
                                state = 25;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4063_);
                                leanh::lean_dec(v___x_4062_);
                                v___x_4065_ = leanh::lean_box(0);
                                v_isShared_4066_ = v_isSharedCheck_4093_;
                                state = 25;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4061_);
                            leanh::lean_dec_ref(v_k_4059_);
                            leanh::lean_dec(v_i_4057_);
                            return v___x_4062_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_k_4059_);
                        leanh::lean_dec(v_y_4058_);
                        leanh::lean_dec(v_i_4057_);
                        return v___x_4060_;
                    }
                }
                8 => {
                    v_fvarId_4094_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    leanh::lean_inc(v_fvarId_4094_);
                    v_i_4095_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    leanh::lean_inc(v_i_4095_);
                    v_y_4096_ = leanh::lean_ctor_get(v_c_3890_, 2);
                    leanh::lean_inc(v_y_4096_);
                    v_k_4097_ = leanh::lean_ctor_get(v_c_3890_, 3);
                    leanh::lean_inc_ref(v_k_4097_);
                    leanh::lean_dec_ref_known(v_c_3890_, 4);
                    v___x_4098_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4094_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_4098_) == 0 {
                        v_a_4099_ = leanh::lean_ctor_get(v___x_4098_, 0);
                        leanh::lean_inc(v_a_4099_);
                        leanh::lean_dec_ref_known(v___x_4098_, 1);
                        v___x_4100_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                            v_y_4096_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                        );
                        if leanh::lean_obj_tag(v___x_4100_) == 0 {
                            v_a_4101_ = leanh::lean_ctor_get(v___x_4100_, 0);
                            v_isSharedCheck_4131_ =
                                (!leanh::lean_is_exclusive(v___x_4100_)) as u8;
                            if v_isSharedCheck_4131_ == 0 {
                                v___x_4103_ = v___x_4100_;
                                v_isShared_4104_ = v_isSharedCheck_4131_;
                                state = 29;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4101_);
                                leanh::lean_dec(v___x_4100_);
                                v___x_4103_ = leanh::lean_box(0);
                                v_isShared_4104_ = v_isSharedCheck_4131_;
                                state = 29;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4099_);
                            leanh::lean_dec_ref(v_k_4097_);
                            leanh::lean_dec(v_i_4095_);
                            return v___x_4100_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_k_4097_);
                        leanh::lean_dec(v_y_4096_);
                        leanh::lean_dec(v_i_4095_);
                        return v___x_4098_;
                    }
                }
                9 => {
                    v_fvarId_4132_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    leanh::lean_inc(v_fvarId_4132_);
                    v_i_4133_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    leanh::lean_inc(v_i_4133_);
                    v_offset_4134_ = leanh::lean_ctor_get(v_c_3890_, 2);
                    leanh::lean_inc(v_offset_4134_);
                    v_y_4135_ = leanh::lean_ctor_get(v_c_3890_, 3);
                    leanh::lean_inc(v_y_4135_);
                    v_ty_4136_ = leanh::lean_ctor_get(v_c_3890_, 4);
                    leanh::lean_inc_ref(v_ty_4136_);
                    v_k_4137_ = leanh::lean_ctor_get(v_c_3890_, 5);
                    leanh::lean_inc_ref(v_k_4137_);
                    leanh::lean_dec_ref_known(v_c_3890_, 6);
                    v_options_4138_ = leanh::lean_ctor_get(v_a_3894_, 2);
                    v___x_4139_ = l_Lean_pp_letVarTypes;
                    v___x_4140_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                        v_options_4138_,
                        v___x_4139_,
                    );
                    if v___x_4140_ == 0 {
                        leanh::lean_dec_ref(v_ty_4136_);
                        v___x_4141_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                            v_fvarId_4132_,
                            v_a_3892_,
                            v_a_3893_,
                            v_a_3894_,
                            v_a_3895_,
                        );
                        if leanh::lean_obj_tag(v___x_4141_) == 0 {
                            v_a_4142_ = leanh::lean_ctor_get(v___x_4141_, 0);
                            v_isSharedCheck_4185_ =
                                (!leanh::lean_is_exclusive(v___x_4141_)) as u8;
                            if v_isSharedCheck_4185_ == 0 {
                                v___x_4144_ = v___x_4141_;
                                v_isShared_4145_ = v_isSharedCheck_4185_;
                                state = 33;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4142_);
                                leanh::lean_dec(v___x_4141_);
                                v___x_4144_ = leanh::lean_box(0);
                                v_isShared_4145_ = v_isSharedCheck_4185_;
                                state = 33;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_k_4137_);
                            leanh::lean_dec(v_y_4135_);
                            leanh::lean_dec(v_offset_4134_);
                            leanh::lean_dec(v_i_4133_);
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
                        if leanh::lean_obj_tag(v___x_4186_) == 0 {
                            v_a_4187_ = leanh::lean_ctor_get(v___x_4186_, 0);
                            leanh::lean_inc(v_a_4187_);
                            leanh::lean_dec_ref_known(v___x_4186_, 1);
                            v___x_4188_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                                v_ty_4136_, v_a_3891_, v_a_3894_, v_a_3895_,
                            );
                            if leanh::lean_obj_tag(v___x_4188_) == 0 {
                                v_a_4189_ = leanh::lean_ctor_get(v___x_4188_, 0);
                                v_isSharedCheck_4235_ =
                                    (!leanh::lean_is_exclusive(v___x_4188_)) as u8;
                                if v_isSharedCheck_4235_ == 0 {
                                    v___x_4191_ = v___x_4188_;
                                    v_isShared_4192_ = v_isSharedCheck_4235_;
                                    state = 39;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4189_);
                                    leanh::lean_dec(v___x_4188_);
                                    v___x_4191_ = leanh::lean_box(0);
                                    v_isShared_4192_ = v_isSharedCheck_4235_;
                                    state = 39;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_4187_);
                                leanh::lean_dec_ref(v_k_4137_);
                                leanh::lean_dec(v_y_4135_);
                                leanh::lean_dec(v_offset_4134_);
                                leanh::lean_dec(v_i_4133_);
                                return v___x_4188_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_k_4137_);
                            leanh::lean_dec_ref(v_ty_4136_);
                            leanh::lean_dec(v_y_4135_);
                            leanh::lean_dec(v_offset_4134_);
                            leanh::lean_dec(v_i_4133_);
                            return v___x_4186_;
                        }
                    }
                }
                10 => {
                    v_fvarId_4236_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    leanh::lean_inc(v_fvarId_4236_);
                    v_cidx_4237_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    leanh::lean_inc(v_cidx_4237_);
                    v_k_4238_ = leanh::lean_ctor_get(v_c_3890_, 2);
                    leanh::lean_inc_ref(v_k_4238_);
                    leanh::lean_dec_ref_known(v_c_3890_, 3);
                    v___x_4239_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4236_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_4239_) == 0 {
                        v_a_4240_ = leanh::lean_ctor_get(v___x_4239_, 0);
                        v_isSharedCheck_4267_ =
                            (!leanh::lean_is_exclusive(v___x_4239_)) as u8;
                        if v_isSharedCheck_4267_ == 0 {
                            v___x_4242_ = v___x_4239_;
                            v_isShared_4243_ = v_isSharedCheck_4267_;
                            state = 45;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4240_);
                            leanh::lean_dec(v___x_4239_);
                            v___x_4242_ = leanh::lean_box(0);
                            v_isShared_4243_ = v_isSharedCheck_4267_;
                            state = 45;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_k_4238_);
                        leanh::lean_dec(v_cidx_4237_);
                        return v___x_4239_;
                    }
                }
                11 => {
                    v_fvarId_4268_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    leanh::lean_inc(v_fvarId_4268_);
                    v_n_4269_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    leanh::lean_inc(v_n_4269_);
                    v_check_4270_ = leanh::lean_ctor_get_uint8(
                        v_c_3890_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_4271_ = leanh::lean_ctor_get_uint8(
                        v_c_3890_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_4272_ = leanh::lean_ctor_get(v_c_3890_, 2);
                    leanh::lean_inc_ref(v_k_4272_);
                    leanh::lean_dec_ref_known(v_c_3890_, 3);
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
                    v_fvarId_4346_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    leanh::lean_inc(v_fvarId_4346_);
                    v_n_4347_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    leanh::lean_inc(v_n_4347_);
                    v_check_4348_ = leanh::lean_ctor_get_uint8(
                        v_c_3890_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v_persistent_4349_ = leanh::lean_ctor_get_uint8(
                        v_c_3890_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                    );
                    v_objs_x3f_4350_ = leanh::lean_ctor_get(v_c_3890_, 2);
                    leanh::lean_inc(v_objs_x3f_4350_);
                    v_k_4351_ = leanh::lean_ctor_get(v_c_3890_, 3);
                    leanh::lean_inc_ref(v_k_4351_);
                    leanh::lean_dec_ref_known(v_c_3890_, 4);
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
                    v_fvarId_4447_ = leanh::lean_ctor_get(v_c_3890_, 0);
                    v_k_4448_ = leanh::lean_ctor_get(v_c_3890_, 1);
                    v_isSharedCheck_4472_ = (!leanh::lean_is_exclusive(v_c_3890_)) as u8;
                    if v_isSharedCheck_4472_ == 0 {
                        v___x_4450_ = v_c_3890_;
                        v_isShared_4451_ = v_isSharedCheck_4472_;
                        state = 70;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_4448_);
                        leanh::lean_inc(v_fvarId_4447_);
                        leanh::lean_dec(v_c_3890_);
                        v___x_4450_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v___x_3902_) == 0 {
                    v_a_3903_ = leanh::lean_ctor_get(v___x_3902_, 0);
                    leanh::lean_inc(v_a_3903_);
                    leanh::lean_dec_ref_known(v___x_3902_, 1);
                    v___x_3904_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3889_, v_k_3898_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_3904_) == 0 {
                        v_a_3905_ = leanh::lean_ctor_get(v___x_3904_, 0);
                        v_isSharedCheck_3919_ =
                            (!leanh::lean_is_exclusive(v___x_3904_)) as u8;
                        if v_isSharedCheck_3919_ == 0 {
                            v___x_3907_ = v___x_3904_;
                            v_isShared_3908_ = v_isSharedCheck_3919_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3905_);
                            leanh::lean_dec(v___x_3904_);
                            v___x_3907_ = leanh::lean_box(0);
                            v_isShared_3908_ = v_isSharedCheck_3919_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3903_);
                        leanh::lean_del_object(v___x_3900_);
                        return v___x_3904_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3900_);
                    leanh::lean_dec_ref(v_k_3898_);
                    return v___x_3902_;
                }
            }
            2 => {
                v___x_3909_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                if v_isShared_3901_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3900_, 5);
                    leanh::lean_ctor_set(v___x_3900_, 1, v___x_3909_);
                    leanh::lean_ctor_set(v___x_3900_, 0, v_a_3903_);
                    v___x_3911_ = v___x_3900_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3918_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3918_, 1, v___x_3909_);
                    v___x_3911_ = v_reuseFailAlloc_3918_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3912_ = leanh::lean_box(1);
                v___x_3913_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3913_, 0, v___x_3911_);
                leanh::lean_ctor_set(v___x_3913_, 1, v___x_3912_);
                v___x_3914_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3914_, 0, v___x_3913_);
                leanh::lean_ctor_set(v___x_3914_, 1, v_a_3905_);
                if v_isShared_3908_ == 0 {
                    leanh::lean_ctor_set(v___x_3907_, 0, v___x_3914_);
                    v___x_3916_ = v___x_3907_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
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
                if leanh::lean_obj_tag(v___x_3926_) == 0 {
                    v_a_3927_ = leanh::lean_ctor_get(v___x_3926_, 0);
                    leanh::lean_inc(v_a_3927_);
                    leanh::lean_dec_ref_known(v___x_3926_, 1);
                    v___x_3928_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3889_, v_k_3922_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_3928_) == 0 {
                        v_a_3929_ = leanh::lean_ctor_get(v___x_3928_, 0);
                        v_isSharedCheck_3945_ =
                            (!leanh::lean_is_exclusive(v___x_3928_)) as u8;
                        if v_isSharedCheck_3945_ == 0 {
                            v___x_3931_ = v___x_3928_;
                            v_isShared_3932_ = v_isSharedCheck_3945_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3929_);
                            leanh::lean_dec(v___x_3928_);
                            v___x_3931_ = leanh::lean_box(0);
                            v_isShared_3932_ = v_isSharedCheck_3945_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3927_);
                        leanh::lean_del_object(v___x_3924_);
                        return v___x_3928_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3924_);
                    leanh::lean_dec_ref(v_k_3922_);
                    return v___x_3926_;
                }
            }
            6 => {
                v___x_3933_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__3;
                if v_isShared_3925_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3924_, 5);
                    leanh::lean_ctor_set(v___x_3924_, 1, v_a_3927_);
                    leanh::lean_ctor_set(v___x_3924_, 0, v___x_3933_);
                    v___x_3935_ = v___x_3924_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3944_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_a_3927_);
                    v___x_3935_ = v_reuseFailAlloc_3944_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3936_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_3937_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3937_, 0, v___x_3935_);
                leanh::lean_ctor_set(v___x_3937_, 1, v___x_3936_);
                v___x_3938_ = leanh::lean_box(1);
                v___x_3939_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3939_, 0, v___x_3937_);
                leanh::lean_ctor_set(v___x_3939_, 1, v___x_3938_);
                v___x_3940_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3940_, 0, v___x_3939_);
                leanh::lean_ctor_set(v___x_3940_, 1, v_a_3929_);
                if v_isShared_3932_ == 0 {
                    leanh::lean_ctor_set(v___x_3931_, 0, v___x_3940_);
                    v___x_3942_ = v___x_3931_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3943_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
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
                if leanh::lean_obj_tag(v___x_3952_) == 0 {
                    v_a_3953_ = leanh::lean_ctor_get(v___x_3952_, 0);
                    leanh::lean_inc(v_a_3953_);
                    leanh::lean_dec_ref_known(v___x_3952_, 1);
                    v___x_3954_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3889_, v_k_3948_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_3954_) == 0 {
                        v_a_3955_ = leanh::lean_ctor_get(v___x_3954_, 0);
                        v_isSharedCheck_3971_ =
                            (!leanh::lean_is_exclusive(v___x_3954_)) as u8;
                        if v_isSharedCheck_3971_ == 0 {
                            v___x_3957_ = v___x_3954_;
                            v_isShared_3958_ = v_isSharedCheck_3971_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3955_);
                            leanh::lean_dec(v___x_3954_);
                            v___x_3957_ = leanh::lean_box(0);
                            v_isShared_3958_ = v_isSharedCheck_3971_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3953_);
                        leanh::lean_del_object(v___x_3950_);
                        return v___x_3954_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3950_);
                    leanh::lean_dec_ref(v_k_3948_);
                    return v___x_3952_;
                }
            }
            10 => {
                v___x_3959_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__5;
                if v_isShared_3951_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3950_, 5);
                    leanh::lean_ctor_set(v___x_3950_, 1, v_a_3953_);
                    leanh::lean_ctor_set(v___x_3950_, 0, v___x_3959_);
                    v___x_3961_ = v___x_3950_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3970_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_a_3953_);
                    v___x_3961_ = v_reuseFailAlloc_3970_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3962_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_3963_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3963_, 0, v___x_3961_);
                leanh::lean_ctor_set(v___x_3963_, 1, v___x_3962_);
                v___x_3964_ = leanh::lean_box(1);
                v___x_3965_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3965_, 0, v___x_3963_);
                leanh::lean_ctor_set(v___x_3965_, 1, v___x_3964_);
                v___x_3966_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3966_, 0, v___x_3965_);
                leanh::lean_ctor_set(v___x_3966_, 1, v_a_3955_);
                if v_isShared_3958_ == 0 {
                    leanh::lean_ctor_set(v___x_3957_, 0, v___x_3966_);
                    v___x_3968_ = v___x_3957_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
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
                if leanh::lean_obj_tag(v___x_3978_) == 0 {
                    v_a_3979_ = leanh::lean_ctor_get(v___x_3978_, 0);
                    leanh::lean_inc(v_a_3979_);
                    leanh::lean_dec_ref_known(v___x_3978_, 1);
                    v___x_3980_ = l_Lean_Compiler_LCNF_PP_ppArgs(
                        v_pu_3889_,
                        v_args_3974_,
                        v_a_3891_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    leanh::lean_dec_ref(v_args_3974_);
                    if leanh::lean_obj_tag(v___x_3980_) == 0 {
                        v_a_3981_ = leanh::lean_ctor_get(v___x_3980_, 0);
                        v_isSharedCheck_3993_ =
                            (!leanh::lean_is_exclusive(v___x_3980_)) as u8;
                        if v_isSharedCheck_3993_ == 0 {
                            v___x_3983_ = v___x_3980_;
                            v_isShared_3984_ = v_isSharedCheck_3993_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3981_);
                            leanh::lean_dec(v___x_3980_);
                            v___x_3983_ = leanh::lean_box(0);
                            v_isShared_3984_ = v_isSharedCheck_3993_;
                            state = 14;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3979_);
                        leanh::lean_del_object(v___x_3976_);
                        return v___x_3980_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3976_);
                    leanh::lean_dec_ref(v_args_3974_);
                    return v___x_3978_;
                }
            }
            14 => {
                v___x_3985_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__7;
                if v_isShared_3977_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3976_, 5);
                    leanh::lean_ctor_set(v___x_3976_, 1, v_a_3979_);
                    leanh::lean_ctor_set(v___x_3976_, 0, v___x_3985_);
                    v___x_3987_ = v___x_3976_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3992_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_a_3979_);
                    v___x_3987_ = v_reuseFailAlloc_3992_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3988_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3988_, 0, v___x_3987_);
                leanh::lean_ctor_set(v___x_3988_, 1, v_a_3981_);
                if v_isShared_3984_ == 0 {
                    leanh::lean_ctor_set(v___x_3983_, 0, v___x_3988_);
                    v___x_3990_ = v___x_3983_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3991_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3988_);
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
                v___x_4012_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4012_, 0, v___x_4011_);
                leanh::lean_ctor_set(v___x_4012_, 1, v_a_4000_);
                v___x_4013_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_4014_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4014_, 0, v___x_4012_);
                leanh::lean_ctor_set(v___x_4014_, 1, v___x_4013_);
                v___x_4015_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4015_, 0, v___x_4014_);
                leanh::lean_ctor_set(v___x_4015_, 1, v_a_4002_);
                v___x_4016_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4016_, 0, v___x_4015_);
                leanh::lean_ctor_set(v___x_4016_, 1, v_a_4007_);
                if v_isShared_4010_ == 0 {
                    leanh::lean_ctor_set(v___x_4009_, 0, v___x_4016_);
                    v___x_4018_ = v___x_4009_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
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
                v___x_4028_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4028_, 0, v___x_4027_);
                leanh::lean_ctor_set(v___x_4028_, 1, v_a_4023_);
                if v_isShared_4026_ == 0 {
                    leanh::lean_ctor_set(v___x_4025_, 0, v___x_4028_);
                    v___x_4030_ = v___x_4025_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4031_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
                    v___x_4030_ = v_reuseFailAlloc_4031_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4030_;
            }
            21 => {
                v_options_4037_ = leanh::lean_ctor_get(v_a_3894_, 2);
                v___x_4038_ = l_Lean_pp_all;
                v___x_4039_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(
                    v_options_4037_,
                    v___x_4038_,
                );
                if v___x_4039_ == 0 {
                    leanh::lean_dec_ref(v_type_4033_);
                    v___x_4040_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__13;
                    if v_isShared_4036_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4035_, 0);
                        leanh::lean_ctor_set(v___x_4035_, 0, v___x_4040_);
                        v___x_4042_ = v___x_4035_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_4043_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4040_);
                        v___x_4042_ = v_reuseFailAlloc_4043_;
                        state = 22;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4035_);
                    v___x_4044_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                        v_type_4033_,
                        v_a_3891_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_4044_) == 0 {
                        v_a_4045_ = leanh::lean_ctor_get(v___x_4044_, 0);
                        v_isSharedCheck_4054_ =
                            (!leanh::lean_is_exclusive(v___x_4044_)) as u8;
                        if v_isSharedCheck_4054_ == 0 {
                            v___x_4047_ = v___x_4044_;
                            v_isShared_4048_ = v_isSharedCheck_4054_;
                            state = 23;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4045_);
                            leanh::lean_dec(v___x_4044_);
                            v___x_4047_ = leanh::lean_box(0);
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
                v___x_4050_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4050_, 0, v___x_4049_);
                leanh::lean_ctor_set(v___x_4050_, 1, v_a_4045_);
                if v_isShared_4048_ == 0 {
                    leanh::lean_ctor_set(v___x_4047_, 0, v___x_4050_);
                    v___x_4052_ = v___x_4047_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4053_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4050_);
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
                if leanh::lean_obj_tag(v___x_4067_) == 0 {
                    v_a_4068_ = leanh::lean_ctor_get(v___x_4067_, 0);
                    v_isSharedCheck_4092_ = (!leanh::lean_is_exclusive(v___x_4067_)) as u8;
                    if v_isSharedCheck_4092_ == 0 {
                        v___x_4070_ = v___x_4067_;
                        v_isShared_4071_ = v_isSharedCheck_4092_;
                        state = 26;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4068_);
                        leanh::lean_dec(v___x_4067_);
                        v___x_4070_ = leanh::lean_box(0);
                        v_isShared_4071_ = v_isSharedCheck_4092_;
                        state = 26;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4065_);
                    leanh::lean_dec(v_a_4063_);
                    leanh::lean_dec(v_a_4061_);
                    leanh::lean_dec(v_i_4057_);
                    return v___x_4067_;
                }
            }
            26 => {
                v___x_4072_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__17;
                v___x_4073_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4073_, 0, v___x_4072_);
                leanh::lean_ctor_set(v___x_4073_, 1, v_a_4061_);
                v___x_4074_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__19;
                v___x_4075_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4075_, 0, v___x_4073_);
                leanh::lean_ctor_set(v___x_4075_, 1, v___x_4074_);
                v___x_4076_ = l_Nat_reprFast(v_i_4057_);
                if v_isShared_4066_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4065_, 3);
                    leanh::lean_ctor_set(v___x_4065_, 0, v___x_4076_);
                    v___x_4078_ = v___x_4065_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4076_);
                    v___x_4078_ = v_reuseFailAlloc_4091_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_4079_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4079_, 0, v___x_4075_);
                leanh::lean_ctor_set(v___x_4079_, 1, v___x_4078_);
                v___x_4080_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__21;
                v___x_4081_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4081_, 0, v___x_4079_);
                leanh::lean_ctor_set(v___x_4081_, 1, v___x_4080_);
                v___x_4082_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4082_, 0, v___x_4081_);
                leanh::lean_ctor_set(v___x_4082_, 1, v_a_4063_);
                v___x_4083_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4084_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4084_, 0, v___x_4082_);
                leanh::lean_ctor_set(v___x_4084_, 1, v___x_4083_);
                v___x_4085_ = leanh::lean_box(1);
                v___x_4086_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4086_, 0, v___x_4084_);
                leanh::lean_ctor_set(v___x_4086_, 1, v___x_4085_);
                v___x_4087_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4087_, 0, v___x_4086_);
                leanh::lean_ctor_set(v___x_4087_, 1, v_a_4068_);
                if v_isShared_4071_ == 0 {
                    leanh::lean_ctor_set(v___x_4070_, 0, v___x_4087_);
                    v___x_4089_ = v___x_4070_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4090_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
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
                if leanh::lean_obj_tag(v___x_4105_) == 0 {
                    v_a_4106_ = leanh::lean_ctor_get(v___x_4105_, 0);
                    v_isSharedCheck_4130_ = (!leanh::lean_is_exclusive(v___x_4105_)) as u8;
                    if v_isSharedCheck_4130_ == 0 {
                        v___x_4108_ = v___x_4105_;
                        v_isShared_4109_ = v_isSharedCheck_4130_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4106_);
                        leanh::lean_dec(v___x_4105_);
                        v___x_4108_ = leanh::lean_box(0);
                        v_isShared_4109_ = v_isSharedCheck_4130_;
                        state = 30;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4103_);
                    leanh::lean_dec(v_a_4101_);
                    leanh::lean_dec(v_a_4099_);
                    leanh::lean_dec(v_i_4095_);
                    return v___x_4105_;
                }
            }
            30 => {
                v___x_4110_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__23;
                v___x_4111_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4111_, 0, v___x_4110_);
                leanh::lean_ctor_set(v___x_4111_, 1, v_a_4099_);
                v___x_4112_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1;
                v___x_4113_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4113_, 0, v___x_4111_);
                leanh::lean_ctor_set(v___x_4113_, 1, v___x_4112_);
                v___x_4114_ = l_Nat_reprFast(v_i_4095_);
                if v_isShared_4104_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4103_, 3);
                    leanh::lean_ctor_set(v___x_4103_, 0, v___x_4114_);
                    v___x_4116_ = v___x_4103_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4129_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4114_);
                    v___x_4116_ = v_reuseFailAlloc_4129_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_4117_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4117_, 0, v___x_4113_);
                leanh::lean_ctor_set(v___x_4117_, 1, v___x_4116_);
                v___x_4118_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__21;
                v___x_4119_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4119_, 0, v___x_4117_);
                leanh::lean_ctor_set(v___x_4119_, 1, v___x_4118_);
                v___x_4120_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4120_, 0, v___x_4119_);
                leanh::lean_ctor_set(v___x_4120_, 1, v_a_4101_);
                v___x_4121_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4122_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4122_, 0, v___x_4120_);
                leanh::lean_ctor_set(v___x_4122_, 1, v___x_4121_);
                v___x_4123_ = leanh::lean_box(1);
                v___x_4124_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4124_, 0, v___x_4122_);
                leanh::lean_ctor_set(v___x_4124_, 1, v___x_4123_);
                v___x_4125_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4125_, 0, v___x_4124_);
                leanh::lean_ctor_set(v___x_4125_, 1, v_a_4106_);
                if v_isShared_4109_ == 0 {
                    leanh::lean_ctor_set(v___x_4108_, 0, v___x_4125_);
                    v___x_4127_ = v___x_4108_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
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
                if leanh::lean_obj_tag(v___x_4146_) == 0 {
                    v_a_4147_ = leanh::lean_ctor_get(v___x_4146_, 0);
                    v_isSharedCheck_4184_ = (!leanh::lean_is_exclusive(v___x_4146_)) as u8;
                    if v_isSharedCheck_4184_ == 0 {
                        v___x_4149_ = v___x_4146_;
                        v_isShared_4150_ = v_isSharedCheck_4184_;
                        state = 34;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4147_);
                        leanh::lean_dec(v___x_4146_);
                        v___x_4149_ = leanh::lean_box(0);
                        v_isShared_4150_ = v_isSharedCheck_4184_;
                        state = 34;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4144_);
                    leanh::lean_dec(v_a_4142_);
                    leanh::lean_dec_ref(v_k_4137_);
                    leanh::lean_dec(v_offset_4134_);
                    leanh::lean_dec(v_i_4133_);
                    return v___x_4146_;
                }
            }
            34 => {
                v___x_4151_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4137_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if leanh::lean_obj_tag(v___x_4151_) == 0 {
                    v_a_4152_ = leanh::lean_ctor_get(v___x_4151_, 0);
                    v_isSharedCheck_4183_ = (!leanh::lean_is_exclusive(v___x_4151_)) as u8;
                    if v_isSharedCheck_4183_ == 0 {
                        v___x_4154_ = v___x_4151_;
                        v_isShared_4155_ = v_isSharedCheck_4183_;
                        state = 35;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4152_);
                        leanh::lean_dec(v___x_4151_);
                        v___x_4154_ = leanh::lean_box(0);
                        v_isShared_4155_ = v_isSharedCheck_4183_;
                        state = 35;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4149_);
                    leanh::lean_dec(v_a_4147_);
                    leanh::lean_del_object(v___x_4144_);
                    leanh::lean_dec(v_a_4142_);
                    leanh::lean_dec(v_offset_4134_);
                    leanh::lean_dec(v_i_4133_);
                    return v___x_4151_;
                }
            }
            35 => {
                v___x_4156_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__25;
                v___x_4157_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4157_, 0, v___x_4156_);
                leanh::lean_ctor_set(v___x_4157_, 1, v_a_4142_);
                v___x_4158_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1;
                v___x_4159_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4159_, 0, v___x_4157_);
                leanh::lean_ctor_set(v___x_4159_, 1, v___x_4158_);
                v___x_4160_ = l_Nat_reprFast(v_i_4133_);
                if v_isShared_4150_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4149_, 3);
                    leanh::lean_ctor_set(v___x_4149_, 0, v___x_4160_);
                    v___x_4162_ = v___x_4149_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4182_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4160_);
                    v___x_4162_ = v_reuseFailAlloc_4182_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___x_4163_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4163_, 0, v___x_4159_);
                leanh::lean_ctor_set(v___x_4163_, 1, v___x_4162_);
                v___x_4164_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11;
                v___x_4165_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4165_, 0, v___x_4163_);
                leanh::lean_ctor_set(v___x_4165_, 1, v___x_4164_);
                v___x_4166_ = l_Nat_reprFast(v_offset_4134_);
                if v_isShared_4145_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4144_, 3);
                    leanh::lean_ctor_set(v___x_4144_, 0, v___x_4166_);
                    v___x_4168_ = v___x_4144_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4181_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4166_);
                    v___x_4168_ = v_reuseFailAlloc_4181_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_4169_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4169_, 0, v___x_4165_);
                leanh::lean_ctor_set(v___x_4169_, 1, v___x_4168_);
                v___x_4170_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__21;
                v___x_4171_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4171_, 0, v___x_4169_);
                leanh::lean_ctor_set(v___x_4171_, 1, v___x_4170_);
                v___x_4172_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4172_, 0, v___x_4171_);
                leanh::lean_ctor_set(v___x_4172_, 1, v_a_4147_);
                v___x_4173_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4174_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4174_, 0, v___x_4172_);
                leanh::lean_ctor_set(v___x_4174_, 1, v___x_4173_);
                v___x_4175_ = leanh::lean_box(1);
                v___x_4176_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4176_, 0, v___x_4174_);
                leanh::lean_ctor_set(v___x_4176_, 1, v___x_4175_);
                v___x_4177_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4177_, 0, v___x_4176_);
                leanh::lean_ctor_set(v___x_4177_, 1, v_a_4152_);
                if v_isShared_4155_ == 0 {
                    leanh::lean_ctor_set(v___x_4154_, 0, v___x_4177_);
                    v___x_4179_ = v___x_4154_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4177_);
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
                if leanh::lean_obj_tag(v___x_4193_) == 0 {
                    v_a_4194_ = leanh::lean_ctor_get(v___x_4193_, 0);
                    v_isSharedCheck_4234_ = (!leanh::lean_is_exclusive(v___x_4193_)) as u8;
                    if v_isSharedCheck_4234_ == 0 {
                        v___x_4196_ = v___x_4193_;
                        v_isShared_4197_ = v_isSharedCheck_4234_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4194_);
                        leanh::lean_dec(v___x_4193_);
                        v___x_4196_ = leanh::lean_box(0);
                        v_isShared_4197_ = v_isSharedCheck_4234_;
                        state = 40;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4191_);
                    leanh::lean_dec(v_a_4189_);
                    leanh::lean_dec(v_a_4187_);
                    leanh::lean_dec_ref(v_k_4137_);
                    leanh::lean_dec(v_offset_4134_);
                    leanh::lean_dec(v_i_4133_);
                    return v___x_4193_;
                }
            }
            40 => {
                v___x_4198_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4137_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if leanh::lean_obj_tag(v___x_4198_) == 0 {
                    v_a_4199_ = leanh::lean_ctor_get(v___x_4198_, 0);
                    v_isSharedCheck_4233_ = (!leanh::lean_is_exclusive(v___x_4198_)) as u8;
                    if v_isSharedCheck_4233_ == 0 {
                        v___x_4201_ = v___x_4198_;
                        v_isShared_4202_ = v_isSharedCheck_4233_;
                        state = 41;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4199_);
                        leanh::lean_dec(v___x_4198_);
                        v___x_4201_ = leanh::lean_box(0);
                        v_isShared_4202_ = v_isSharedCheck_4233_;
                        state = 41;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4196_);
                    leanh::lean_dec(v_a_4194_);
                    leanh::lean_del_object(v___x_4191_);
                    leanh::lean_dec(v_a_4189_);
                    leanh::lean_dec(v_a_4187_);
                    leanh::lean_dec(v_offset_4134_);
                    leanh::lean_dec(v_i_4133_);
                    return v___x_4198_;
                }
            }
            41 => {
                v___x_4203_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__25;
                v___x_4204_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4204_, 0, v___x_4203_);
                leanh::lean_ctor_set(v___x_4204_, 1, v_a_4187_);
                v___x_4205_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1;
                v___x_4206_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4206_, 0, v___x_4204_);
                leanh::lean_ctor_set(v___x_4206_, 1, v___x_4205_);
                v___x_4207_ = l_Nat_reprFast(v_i_4133_);
                if v_isShared_4197_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4196_, 3);
                    leanh::lean_ctor_set(v___x_4196_, 0, v___x_4207_);
                    v___x_4209_ = v___x_4196_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4207_);
                    v___x_4209_ = v_reuseFailAlloc_4232_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                v___x_4210_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4210_, 0, v___x_4206_);
                leanh::lean_ctor_set(v___x_4210_, 1, v___x_4209_);
                v___x_4211_ = l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11;
                v___x_4212_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4212_, 0, v___x_4210_);
                leanh::lean_ctor_set(v___x_4212_, 1, v___x_4211_);
                v___x_4213_ = l_Nat_reprFast(v_offset_4134_);
                if v_isShared_4192_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4191_, 3);
                    leanh::lean_ctor_set(v___x_4191_, 0, v___x_4213_);
                    v___x_4215_ = v___x_4191_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4213_);
                    v___x_4215_ = v_reuseFailAlloc_4231_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_4216_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4216_, 0, v___x_4212_);
                leanh::lean_ctor_set(v___x_4216_, 1, v___x_4215_);
                v___x_4217_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__27;
                v___x_4218_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4218_, 0, v___x_4216_);
                leanh::lean_ctor_set(v___x_4218_, 1, v___x_4217_);
                v___x_4219_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4219_, 0, v___x_4218_);
                leanh::lean_ctor_set(v___x_4219_, 1, v_a_4189_);
                v___x_4220_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
                v___x_4221_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4221_, 0, v___x_4219_);
                leanh::lean_ctor_set(v___x_4221_, 1, v___x_4220_);
                v___x_4222_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4222_, 0, v___x_4221_);
                leanh::lean_ctor_set(v___x_4222_, 1, v_a_4194_);
                v___x_4223_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4224_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4224_, 0, v___x_4222_);
                leanh::lean_ctor_set(v___x_4224_, 1, v___x_4223_);
                v___x_4225_ = leanh::lean_box(1);
                v___x_4226_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4226_, 0, v___x_4224_);
                leanh::lean_ctor_set(v___x_4226_, 1, v___x_4225_);
                v___x_4227_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4227_, 0, v___x_4226_);
                leanh::lean_ctor_set(v___x_4227_, 1, v_a_4199_);
                if v_isShared_4202_ == 0 {
                    leanh::lean_ctor_set(v___x_4201_, 0, v___x_4227_);
                    v___x_4229_ = v___x_4201_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4230_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
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
                if leanh::lean_obj_tag(v___x_4244_) == 0 {
                    v_a_4245_ = leanh::lean_ctor_get(v___x_4244_, 0);
                    v_isSharedCheck_4266_ = (!leanh::lean_is_exclusive(v___x_4244_)) as u8;
                    if v_isSharedCheck_4266_ == 0 {
                        v___x_4247_ = v___x_4244_;
                        v_isShared_4248_ = v_isSharedCheck_4266_;
                        state = 46;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4245_);
                        leanh::lean_dec(v___x_4244_);
                        v___x_4247_ = leanh::lean_box(0);
                        v_isShared_4248_ = v_isSharedCheck_4266_;
                        state = 46;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4242_);
                    leanh::lean_dec(v_a_4240_);
                    leanh::lean_dec(v_cidx_4237_);
                    return v___x_4244_;
                }
            }
            46 => {
                v___x_4249_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__29;
                v___x_4250_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4250_, 0, v___x_4249_);
                leanh::lean_ctor_set(v___x_4250_, 1, v_a_4240_);
                v___x_4251_ = l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3;
                v___x_4252_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4252_, 0, v___x_4250_);
                leanh::lean_ctor_set(v___x_4252_, 1, v___x_4251_);
                v___x_4253_ = l_Nat_reprFast(v_cidx_4237_);
                if v_isShared_4243_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4242_, 3);
                    leanh::lean_ctor_set(v___x_4242_, 0, v___x_4253_);
                    v___x_4255_ = v___x_4242_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4265_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4253_);
                    v___x_4255_ = v_reuseFailAlloc_4265_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                v___x_4256_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4256_, 0, v___x_4252_);
                leanh::lean_ctor_set(v___x_4256_, 1, v___x_4255_);
                v___x_4257_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4258_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4258_, 0, v___x_4256_);
                leanh::lean_ctor_set(v___x_4258_, 1, v___x_4257_);
                v___x_4259_ = leanh::lean_box(1);
                v___x_4260_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4260_, 0, v___x_4258_);
                leanh::lean_ctor_set(v___x_4260_, 1, v___x_4259_);
                v___x_4261_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4261_, 0, v___x_4260_);
                leanh::lean_ctor_set(v___x_4261_, 1, v_a_4245_);
                if v_isShared_4248_ == 0 {
                    leanh::lean_ctor_set(v___x_4247_, 0, v___x_4261_);
                    v___x_4263_ = v___x_4247_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4264_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4261_);
                    v___x_4263_ = v_reuseFailAlloc_4264_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4263_;
            }
            49 => {
                leanh::lean_inc_ref(v___y_4274_);
                v_ann_4276_ = lean_string_append(v___y_4274_, v___y_4275_);
                v___x_4277_ = leanh::lean_unsigned_to_nat(1);
                v___x_4278_ = lean_nat_dec_eq(v_n_4269_, v___x_4277_);
                if v___x_4278_ == 0 {
                    v___x_4279_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4268_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_4279_) == 0 {
                        v_a_4280_ = leanh::lean_ctor_get(v___x_4279_, 0);
                        v_isSharedCheck_4311_ =
                            (!leanh::lean_is_exclusive(v___x_4279_)) as u8;
                        if v_isSharedCheck_4311_ == 0 {
                            v___x_4282_ = v___x_4279_;
                            v_isShared_4283_ = v_isSharedCheck_4311_;
                            state = 50;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4280_);
                            leanh::lean_dec(v___x_4279_);
                            v___x_4282_ = leanh::lean_box(0);
                            v_isShared_4283_ = v_isSharedCheck_4311_;
                            state = 50;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_ann_4276_);
                        leanh::lean_dec_ref(v_k_4272_);
                        leanh::lean_dec(v_n_4269_);
                        return v___x_4279_;
                    }
                } else {
                    leanh::lean_dec(v_n_4269_);
                    v___x_4312_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4268_,
                        v_a_3892_,
                        v_a_3893_,
                        v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_4312_) == 0 {
                        v_a_4313_ = leanh::lean_ctor_get(v___x_4312_, 0);
                        v_isSharedCheck_4339_ =
                            (!leanh::lean_is_exclusive(v___x_4312_)) as u8;
                        if v_isSharedCheck_4339_ == 0 {
                            v___x_4315_ = v___x_4312_;
                            v_isShared_4316_ = v_isSharedCheck_4339_;
                            state = 54;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4313_);
                            leanh::lean_dec(v___x_4312_);
                            v___x_4315_ = leanh::lean_box(0);
                            v_isShared_4316_ = v_isSharedCheck_4339_;
                            state = 54;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_ann_4276_);
                        leanh::lean_dec_ref(v_k_4272_);
                        return v___x_4312_;
                    }
                }
            }
            50 => {
                v___x_4284_ = l_Lean_Compiler_LCNF_PP_ppCode(
                    v_pu_3889_, v_k_4272_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_,
                );
                if leanh::lean_obj_tag(v___x_4284_) == 0 {
                    v_a_4285_ = leanh::lean_ctor_get(v___x_4284_, 0);
                    v_isSharedCheck_4310_ = (!leanh::lean_is_exclusive(v___x_4284_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4287_ = v___x_4284_;
                        v_isShared_4288_ = v_isSharedCheck_4310_;
                        state = 51;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4285_);
                        leanh::lean_dec(v___x_4284_);
                        v___x_4287_ = leanh::lean_box(0);
                        v_isShared_4288_ = v_isSharedCheck_4310_;
                        state = 51;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4282_);
                    leanh::lean_dec(v_a_4280_);
                    leanh::lean_dec_ref(v_ann_4276_);
                    leanh::lean_dec(v_n_4269_);
                    return v___x_4284_;
                }
            }
            51 => {
                v___x_4289_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__31;
                v___x_4290_ = l_Nat_reprFast(v_n_4269_);
                if v_isShared_4283_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4282_, 3);
                    leanh::lean_ctor_set(v___x_4282_, 0, v___x_4290_);
                    v___x_4292_ = v___x_4282_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4290_);
                    v___x_4292_ = v_reuseFailAlloc_4309_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                v___x_4293_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4293_, 0, v___x_4289_);
                leanh::lean_ctor_set(v___x_4293_, 1, v___x_4292_);
                v___x_4294_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3;
                v___x_4295_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4295_, 0, v___x_4293_);
                leanh::lean_ctor_set(v___x_4295_, 1, v___x_4294_);
                v___x_4296_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4296_, 0, v_ann_4276_);
                v___x_4297_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4297_, 0, v___x_4295_);
                leanh::lean_ctor_set(v___x_4297_, 1, v___x_4296_);
                v___x_4298_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_4299_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4299_, 0, v___x_4297_);
                leanh::lean_ctor_set(v___x_4299_, 1, v___x_4298_);
                v___x_4300_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4300_, 0, v___x_4299_);
                leanh::lean_ctor_set(v___x_4300_, 1, v_a_4280_);
                v___x_4301_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4302_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4302_, 0, v___x_4300_);
                leanh::lean_ctor_set(v___x_4302_, 1, v___x_4301_);
                v___x_4303_ = leanh::lean_box(1);
                v___x_4304_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4304_, 0, v___x_4302_);
                leanh::lean_ctor_set(v___x_4304_, 1, v___x_4303_);
                v___x_4305_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4305_, 0, v___x_4304_);
                leanh::lean_ctor_set(v___x_4305_, 1, v_a_4285_);
                if v_isShared_4288_ == 0 {
                    leanh::lean_ctor_set(v___x_4287_, 0, v___x_4305_);
                    v___x_4307_ = v___x_4287_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
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
                if leanh::lean_obj_tag(v___x_4317_) == 0 {
                    v_a_4318_ = leanh::lean_ctor_get(v___x_4317_, 0);
                    v_isSharedCheck_4338_ = (!leanh::lean_is_exclusive(v___x_4317_)) as u8;
                    if v_isSharedCheck_4338_ == 0 {
                        v___x_4320_ = v___x_4317_;
                        v_isShared_4321_ = v_isSharedCheck_4338_;
                        state = 55;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4318_);
                        leanh::lean_dec(v___x_4317_);
                        v___x_4320_ = leanh::lean_box(0);
                        v_isShared_4321_ = v_isSharedCheck_4338_;
                        state = 55;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4315_);
                    leanh::lean_dec(v_a_4313_);
                    leanh::lean_dec_ref(v_ann_4276_);
                    return v___x_4317_;
                }
            }
            55 => {
                v___x_4322_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__33;
                if v_isShared_4316_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4315_, 3);
                    leanh::lean_ctor_set(v___x_4315_, 0, v_ann_4276_);
                    v___x_4324_ = v___x_4315_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_ann_4276_);
                    v___x_4324_ = v_reuseFailAlloc_4337_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v___x_4325_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4325_, 0, v___x_4322_);
                leanh::lean_ctor_set(v___x_4325_, 1, v___x_4324_);
                v___x_4326_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_4327_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4327_, 0, v___x_4325_);
                leanh::lean_ctor_set(v___x_4327_, 1, v___x_4326_);
                v___x_4328_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4328_, 0, v___x_4327_);
                leanh::lean_ctor_set(v___x_4328_, 1, v_a_4313_);
                v___x_4329_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4330_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4330_, 0, v___x_4328_);
                leanh::lean_ctor_set(v___x_4330_, 1, v___x_4329_);
                v___x_4331_ = leanh::lean_box(1);
                v___x_4332_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4332_, 0, v___x_4330_);
                leanh::lean_ctor_set(v___x_4332_, 1, v___x_4331_);
                v___x_4333_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4333_, 0, v___x_4332_);
                leanh::lean_ctor_set(v___x_4333_, 1, v_a_4318_);
                if v_isShared_4321_ == 0 {
                    leanh::lean_ctor_set(v___x_4320_, 0, v___x_4333_);
                    v___x_4335_ = v___x_4320_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4333_);
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
                v___x_4359_ = leanh::lean_unsigned_to_nat(1);
                v___x_4360_ = lean_nat_dec_eq(v_n_4347_, v___x_4359_);
                if v___x_4360_ == 0 {
                    v___x_4361_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4346_,
                        v___y_4355_,
                        v___y_4356_,
                        v___y_4357_,
                        v___y_4358_,
                    );
                    if leanh::lean_obj_tag(v___x_4361_) == 0 {
                        v_a_4362_ = leanh::lean_ctor_get(v___x_4361_, 0);
                        v_isSharedCheck_4393_ =
                            (!leanh::lean_is_exclusive(v___x_4361_)) as u8;
                        if v_isSharedCheck_4393_ == 0 {
                            v___x_4364_ = v___x_4361_;
                            v_isShared_4365_ = v_isSharedCheck_4393_;
                            state = 60;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4362_);
                            leanh::lean_dec(v___x_4361_);
                            v___x_4364_ = leanh::lean_box(0);
                            v_isShared_4365_ = v_isSharedCheck_4393_;
                            state = 60;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_ann_4353_);
                        leanh::lean_dec_ref(v_k_4351_);
                        leanh::lean_dec(v_n_4347_);
                        return v___x_4361_;
                    }
                } else {
                    leanh::lean_dec(v_n_4347_);
                    v___x_4394_ = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(
                        v_fvarId_4346_,
                        v___y_4355_,
                        v___y_4356_,
                        v___y_4357_,
                        v___y_4358_,
                    );
                    if leanh::lean_obj_tag(v___x_4394_) == 0 {
                        v_a_4395_ = leanh::lean_ctor_get(v___x_4394_, 0);
                        v_isSharedCheck_4421_ =
                            (!leanh::lean_is_exclusive(v___x_4394_)) as u8;
                        if v_isSharedCheck_4421_ == 0 {
                            v___x_4397_ = v___x_4394_;
                            v_isShared_4398_ = v_isSharedCheck_4421_;
                            state = 64;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4395_);
                            leanh::lean_dec(v___x_4394_);
                            v___x_4397_ = leanh::lean_box(0);
                            v_isShared_4398_ = v_isSharedCheck_4421_;
                            state = 64;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_ann_4353_);
                        leanh::lean_dec_ref(v_k_4351_);
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
                if leanh::lean_obj_tag(v___x_4366_) == 0 {
                    v_a_4367_ = leanh::lean_ctor_get(v___x_4366_, 0);
                    v_isSharedCheck_4392_ = (!leanh::lean_is_exclusive(v___x_4366_)) as u8;
                    if v_isSharedCheck_4392_ == 0 {
                        v___x_4369_ = v___x_4366_;
                        v_isShared_4370_ = v_isSharedCheck_4392_;
                        state = 61;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4367_);
                        leanh::lean_dec(v___x_4366_);
                        v___x_4369_ = leanh::lean_box(0);
                        v_isShared_4370_ = v_isSharedCheck_4392_;
                        state = 61;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4364_);
                    leanh::lean_dec(v_a_4362_);
                    leanh::lean_dec_ref(v_ann_4353_);
                    leanh::lean_dec(v_n_4347_);
                    return v___x_4366_;
                }
            }
            61 => {
                v___x_4371_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__37;
                v___x_4372_ = l_Nat_reprFast(v_n_4347_);
                if v_isShared_4365_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4364_, 3);
                    leanh::lean_ctor_set(v___x_4364_, 0, v___x_4372_);
                    v___x_4374_ = v___x_4364_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_4391_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4372_);
                    v___x_4374_ = v_reuseFailAlloc_4391_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                v___x_4375_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4375_, 0, v___x_4371_);
                leanh::lean_ctor_set(v___x_4375_, 1, v___x_4374_);
                v___x_4376_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3;
                v___x_4377_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4377_, 0, v___x_4375_);
                leanh::lean_ctor_set(v___x_4377_, 1, v___x_4376_);
                v___x_4378_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4378_, 0, v_ann_4353_);
                v___x_4379_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4379_, 0, v___x_4377_);
                leanh::lean_ctor_set(v___x_4379_, 1, v___x_4378_);
                v___x_4380_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_4381_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4381_, 0, v___x_4379_);
                leanh::lean_ctor_set(v___x_4381_, 1, v___x_4380_);
                v___x_4382_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4382_, 0, v___x_4381_);
                leanh::lean_ctor_set(v___x_4382_, 1, v_a_4362_);
                v___x_4383_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4384_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4384_, 0, v___x_4382_);
                leanh::lean_ctor_set(v___x_4384_, 1, v___x_4383_);
                v___x_4385_ = leanh::lean_box(1);
                v___x_4386_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4386_, 0, v___x_4384_);
                leanh::lean_ctor_set(v___x_4386_, 1, v___x_4385_);
                v___x_4387_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4387_, 0, v___x_4386_);
                leanh::lean_ctor_set(v___x_4387_, 1, v_a_4367_);
                if v_isShared_4370_ == 0 {
                    leanh::lean_ctor_set(v___x_4369_, 0, v___x_4387_);
                    v___x_4389_ = v___x_4369_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_4390_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4387_);
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
                if leanh::lean_obj_tag(v___x_4399_) == 0 {
                    v_a_4400_ = leanh::lean_ctor_get(v___x_4399_, 0);
                    v_isSharedCheck_4420_ = (!leanh::lean_is_exclusive(v___x_4399_)) as u8;
                    if v_isSharedCheck_4420_ == 0 {
                        v___x_4402_ = v___x_4399_;
                        v_isShared_4403_ = v_isSharedCheck_4420_;
                        state = 65;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4400_);
                        leanh::lean_dec(v___x_4399_);
                        v___x_4402_ = leanh::lean_box(0);
                        v_isShared_4403_ = v_isSharedCheck_4420_;
                        state = 65;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4397_);
                    leanh::lean_dec(v_a_4395_);
                    leanh::lean_dec_ref(v_ann_4353_);
                    return v___x_4399_;
                }
            }
            65 => {
                v___x_4404_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__39;
                if v_isShared_4398_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4397_, 3);
                    leanh::lean_ctor_set(v___x_4397_, 0, v_ann_4353_);
                    v___x_4406_ = v___x_4397_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_4419_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_ann_4353_);
                    v___x_4406_ = v_reuseFailAlloc_4419_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                v___x_4407_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4407_, 0, v___x_4404_);
                leanh::lean_ctor_set(v___x_4407_, 1, v___x_4406_);
                v___x_4408_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1;
                v___x_4409_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4409_, 0, v___x_4407_);
                leanh::lean_ctor_set(v___x_4409_, 1, v___x_4408_);
                v___x_4410_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4410_, 0, v___x_4409_);
                leanh::lean_ctor_set(v___x_4410_, 1, v_a_4395_);
                v___x_4411_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4412_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4412_, 0, v___x_4410_);
                leanh::lean_ctor_set(v___x_4412_, 1, v___x_4411_);
                v___x_4413_ = leanh::lean_box(1);
                v___x_4414_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4414_, 0, v___x_4412_);
                leanh::lean_ctor_set(v___x_4414_, 1, v___x_4413_);
                v___x_4415_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4415_, 0, v___x_4414_);
                leanh::lean_ctor_set(v___x_4415_, 1, v_a_4400_);
                if v_isShared_4403_ == 0 {
                    leanh::lean_ctor_set(v___x_4402_, 0, v___x_4415_);
                    v___x_4417_ = v___x_4402_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4418_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
                    v___x_4417_ = v_reuseFailAlloc_4418_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_4417_;
            }
            68 => {
                if leanh::lean_obj_tag(v_objs_x3f_4350_) == 1 {
                    v_val_4429_ = leanh::lean_ctor_get(v_objs_x3f_4350_, 0);
                    leanh::lean_inc(v_val_4429_);
                    leanh::lean_dec_ref_known(v_objs_x3f_4350_, 1);
                    v___x_4430_ = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0;
                    v___x_4431_ = l_Nat_reprFast(v_val_4429_);
                    v___x_4432_ = lean_string_append(v___x_4430_, v___x_4431_);
                    leanh::lean_dec_ref(v___x_4431_);
                    v___x_4433_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__40;
                    v___x_4434_ = lean_string_append(v___x_4432_, v___x_4433_);
                    v_ann_4435_ = lean_string_append(v_ann_4423_, v___x_4434_);
                    leanh::lean_dec_ref(v___x_4434_);
                    v_ann_4353_ = v_ann_4435_;
                    v___y_4354_ = v___y_4424_;
                    v___y_4355_ = v___y_4425_;
                    v___y_4356_ = v___y_4426_;
                    v___y_4357_ = v___y_4427_;
                    v___y_4358_ = v___y_4428_;
                    state = 59;
                    continue;
                } else {
                    leanh::lean_dec(v_objs_x3f_4350_);
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
                    leanh::lean_inc_ref(v_ann_4437_);
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
                    leanh::lean_inc_ref(v_ann_4437_);
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
                if leanh::lean_obj_tag(v___x_4452_) == 0 {
                    v_a_4453_ = leanh::lean_ctor_get(v___x_4452_, 0);
                    leanh::lean_inc(v_a_4453_);
                    leanh::lean_dec_ref_known(v___x_4452_, 1);
                    v___x_4454_ = l_Lean_Compiler_LCNF_PP_ppCode(
                        v_pu_3889_, v_k_4448_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_,
                        v_a_3895_,
                    );
                    if leanh::lean_obj_tag(v___x_4454_) == 0 {
                        v_a_4455_ = leanh::lean_ctor_get(v___x_4454_, 0);
                        v_isSharedCheck_4471_ =
                            (!leanh::lean_is_exclusive(v___x_4454_)) as u8;
                        if v_isSharedCheck_4471_ == 0 {
                            v___x_4457_ = v___x_4454_;
                            v_isShared_4458_ = v_isSharedCheck_4471_;
                            state = 71;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4455_);
                            leanh::lean_dec(v___x_4454_);
                            v___x_4457_ = leanh::lean_box(0);
                            v_isShared_4458_ = v_isSharedCheck_4471_;
                            state = 71;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4453_);
                        leanh::lean_del_object(v___x_4450_);
                        return v___x_4454_;
                    }
                } else {
                    leanh::lean_del_object(v___x_4450_);
                    leanh::lean_dec_ref(v_k_4448_);
                    return v___x_4452_;
                }
            }
            71 => {
                v___x_4459_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__42;
                if v_isShared_4451_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4450_, 5);
                    leanh::lean_ctor_set(v___x_4450_, 1, v_a_4453_);
                    leanh::lean_ctor_set(v___x_4450_, 0, v___x_4459_);
                    v___x_4461_ = v___x_4450_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_4470_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4470_, 1, v_a_4453_);
                    v___x_4461_ = v_reuseFailAlloc_4470_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                v___x_4462_ = l_Lean_Compiler_LCNF_PP_ppCode___closed__1;
                v___x_4463_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4463_, 0, v___x_4461_);
                leanh::lean_ctor_set(v___x_4463_, 1, v___x_4462_);
                v___x_4464_ = leanh::lean_box(1);
                v___x_4465_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4465_, 0, v___x_4463_);
                leanh::lean_ctor_set(v___x_4465_, 1, v___x_4464_);
                v___x_4466_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4466_, 0, v___x_4465_);
                leanh::lean_ctor_set(v___x_4466_, 1, v_a_4455_);
                if v_isShared_4458_ == 0 {
                    leanh::lean_ctor_set(v___x_4457_, 0, v___x_4466_);
                    v___x_4468_ = v___x_4457_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_4469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
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
    mut v_funDecl_4474_: *mut leanh::LeanObject,
    mut v_a_4475_: *mut leanh::LeanObject,
    mut v_a_4476_: *mut leanh::LeanObject,
    mut v_a_4477_: *mut leanh::LeanObject,
    mut v_a_4478_: *mut leanh::LeanObject,
    mut v_a_4479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderName_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4493_: u8 = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4498_: u8 = 0;
    let mut v___x_4499_: u8 = 0;
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4515_: u8 = 0;
    let mut v_isSharedCheck_4516_: u8 = 0;
    let mut v_a_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4520_: u8 = 0;
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_binderName_4481_ = leanh::lean_ctor_get(v_funDecl_4474_, 1);
                leanh::lean_inc(v_binderName_4481_);
                v_params_4482_ = leanh::lean_ctor_get(v_funDecl_4474_, 2);
                leanh::lean_inc_ref(v_params_4482_);
                v_type_4483_ = leanh::lean_ctor_get(v_funDecl_4474_, 3);
                leanh::lean_inc_ref(v_type_4483_);
                v_value_4484_ = leanh::lean_ctor_get(v_funDecl_4474_, 4);
                leanh::lean_inc_ref(v_value_4484_);
                leanh::lean_dec_ref(v_funDecl_4474_);
                v___x_4485_ = l_Lean_Compiler_LCNF_PP_ppParams(
                    v_pu_4473_,
                    v_params_4482_,
                    v_a_4475_,
                    v_a_4476_,
                    v_a_4477_,
                    v_a_4478_,
                    v_a_4479_,
                );
                if leanh::lean_obj_tag(v___x_4485_) == 0 {
                    v_a_4486_ = leanh::lean_ctor_get(v___x_4485_, 0);
                    leanh::lean_inc(v_a_4486_);
                    leanh::lean_dec_ref_known(v___x_4485_, 1);
                    v___x_4487_ = l_Lean_Compiler_LCNF_PP_getFunType(
                        v_pu_4473_,
                        v_params_4482_,
                        v_type_4483_,
                        v_a_4478_,
                        v_a_4479_,
                    );
                    if leanh::lean_obj_tag(v___x_4487_) == 0 {
                        v_a_4488_ = leanh::lean_ctor_get(v___x_4487_, 0);
                        leanh::lean_inc(v_a_4488_);
                        leanh::lean_dec_ref_known(v___x_4487_, 1);
                        v___x_4489_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                            v_a_4488_, v_a_4475_, v_a_4478_, v_a_4479_,
                        );
                        if leanh::lean_obj_tag(v___x_4489_) == 0 {
                            v_a_4490_ = leanh::lean_ctor_get(v___x_4489_, 0);
                            v_isSharedCheck_4516_ =
                                (!leanh::lean_is_exclusive(v___x_4489_)) as u8;
                            if v_isSharedCheck_4516_ == 0 {
                                v___x_4492_ = v___x_4489_;
                                v_isShared_4493_ = v_isSharedCheck_4516_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4490_);
                                leanh::lean_dec(v___x_4489_);
                                v___x_4492_ = leanh::lean_box(0);
                                v_isShared_4493_ = v_isSharedCheck_4516_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4486_);
                            leanh::lean_dec_ref(v_value_4484_);
                            leanh::lean_dec(v_binderName_4481_);
                            return v___x_4489_;
                        }
                    } else {
                        leanh::lean_dec(v_a_4486_);
                        leanh::lean_dec_ref(v_value_4484_);
                        leanh::lean_dec(v_binderName_4481_);
                        v_a_4517_ = leanh::lean_ctor_get(v___x_4487_, 0);
                        v_isSharedCheck_4524_ =
                            (!leanh::lean_is_exclusive(v___x_4487_)) as u8;
                        if v_isSharedCheck_4524_ == 0 {
                            v___x_4519_ = v___x_4487_;
                            v_isShared_4520_ = v_isSharedCheck_4524_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4517_);
                            leanh::lean_dec(v___x_4487_);
                            v___x_4519_ = leanh::lean_box(0);
                            v_isShared_4520_ = v_isSharedCheck_4524_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_value_4484_);
                    leanh::lean_dec_ref(v_type_4483_);
                    leanh::lean_dec_ref(v_params_4482_);
                    leanh::lean_dec(v_binderName_4481_);
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
                if leanh::lean_obj_tag(v___x_4494_) == 0 {
                    v_a_4495_ = leanh::lean_ctor_get(v___x_4494_, 0);
                    v_isSharedCheck_4515_ = (!leanh::lean_is_exclusive(v___x_4494_)) as u8;
                    if v_isSharedCheck_4515_ == 0 {
                        v___x_4497_ = v___x_4494_;
                        v_isShared_4498_ = v_isSharedCheck_4515_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4495_);
                        leanh::lean_dec(v___x_4494_);
                        v___x_4497_ = leanh::lean_box(0);
                        v_isShared_4498_ = v_isSharedCheck_4515_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4492_);
                    leanh::lean_dec(v_a_4490_);
                    leanh::lean_dec(v_a_4486_);
                    leanh::lean_dec(v_binderName_4481_);
                    return v___x_4494_;
                }
            }
            2 => {
                v___x_4499_ = 1;
                v___x_4500_ = l_Lean_Name_toString(v_binderName_4481_, v___x_4499_);
                if v_isShared_4493_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4492_, 3);
                    leanh::lean_ctor_set(v___x_4492_, 0, v___x_4500_);
                    v___x_4502_ = v___x_4492_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4514_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4500_);
                    v___x_4502_ = v_reuseFailAlloc_4514_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4503_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4503_, 0, v___x_4502_);
                leanh::lean_ctor_set(v___x_4503_, 1, v_a_4486_);
                v___x_4504_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_4505_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4505_, 0, v___x_4503_);
                leanh::lean_ctor_set(v___x_4505_, 1, v___x_4504_);
                v___x_4506_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4506_, 0, v___x_4505_);
                leanh::lean_ctor_set(v___x_4506_, 1, v_a_4490_);
                v___x_4507_ = l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1;
                v___x_4508_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4508_, 0, v___x_4506_);
                leanh::lean_ctor_set(v___x_4508_, 1, v___x_4507_);
                v___x_4509_ = l_Std_Format_indentD(v_a_4495_);
                v___x_4510_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4510_, 0, v___x_4508_);
                leanh::lean_ctor_set(v___x_4510_, 1, v___x_4509_);
                if v_isShared_4498_ == 0 {
                    leanh::lean_ctor_set(v___x_4497_, 0, v___x_4510_);
                    v___x_4512_ = v___x_4497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
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
                    v_reuseFailAlloc_4523_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
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
    mut v_pu_4525_: *mut leanh::LeanObject,
    mut v_funDecl_4526_: *mut leanh::LeanObject,
    mut v_a_4527_: *mut leanh::LeanObject,
    mut v_a_4528_: *mut leanh::LeanObject,
    mut v_a_4529_: *mut leanh::LeanObject,
    mut v_a_4530_: *mut leanh::LeanObject,
    mut v_a_4531_: *mut leanh::LeanObject,
    mut v_a_4532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4533_: u8 = 0;
    let mut v_res_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4533_ = (leanh::lean_unbox(v_pu_4525_) as u8);
    v_res_4534_ = l_Lean_Compiler_LCNF_PP_ppFunDecl(
        v_pu_boxed_4533_,
        v_funDecl_4526_,
        v_a_4527_,
        v_a_4528_,
        v_a_4529_,
        v_a_4530_,
        v_a_4531_,
    );
    leanh::lean_dec(v_a_4531_);
    leanh::lean_dec_ref(v_a_4530_);
    leanh::lean_dec(v_a_4529_);
    leanh::lean_dec_ref(v_a_4528_);
    leanh::lean_dec_ref(v_a_4527_);
    return v_res_4534_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppCode___boxed(
    mut v_pu_4535_: *mut leanh::LeanObject,
    mut v_c_4536_: *mut leanh::LeanObject,
    mut v_a_4537_: *mut leanh::LeanObject,
    mut v_a_4538_: *mut leanh::LeanObject,
    mut v_a_4539_: *mut leanh::LeanObject,
    mut v_a_4540_: *mut leanh::LeanObject,
    mut v_a_4541_: *mut leanh::LeanObject,
    mut v_a_4542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4543_: u8 = 0;
    let mut v_res_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4543_ = (leanh::lean_unbox(v_pu_4535_) as u8);
    v_res_4544_ = l_Lean_Compiler_LCNF_PP_ppCode(
        v_pu_boxed_4543_,
        v_c_4536_,
        v_a_4537_,
        v_a_4538_,
        v_a_4539_,
        v_a_4540_,
        v_a_4541_,
    );
    leanh::lean_dec(v_a_4541_);
    leanh::lean_dec_ref(v_a_4540_);
    leanh::lean_dec(v_a_4539_);
    leanh::lean_dec_ref(v_a_4538_);
    leanh::lean_dec_ref(v_a_4537_);
    return v_res_4544_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_ppDeclValue(
    mut v_pu_4548_: u8,
    mut v_b_4549_: *mut leanh::LeanObject,
    mut v_a_4550_: *mut leanh::LeanObject,
    mut v_a_4551_: *mut leanh::LeanObject,
    mut v_a_4552_: *mut leanh::LeanObject,
    mut v_a_4553_: *mut leanh::LeanObject,
    mut v_a_4554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_code_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4560_: u8 = 0;
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4565_: u8 = 0;
    let mut v_unused_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_b_4549_) == 0 {
                    v_code_4556_ = leanh::lean_ctor_get(v_b_4549_, 0);
                    leanh::lean_inc_ref(v_code_4556_);
                    leanh::lean_dec_ref_known(v_b_4549_, 1);
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
                    v_isSharedCheck_4565_ = (!leanh::lean_is_exclusive(v_b_4549_)) as u8;
                    if v_isSharedCheck_4565_ == 0 {
                        v_unused_4566_ = leanh::lean_ctor_get(v_b_4549_, 0);
                        leanh::lean_dec(v_unused_4566_);
                        v___x_4559_ = v_b_4549_;
                        v_isShared_4560_ = v_isSharedCheck_4565_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_b_4549_);
                        v___x_4559_ = leanh::lean_box(0);
                        v_isShared_4560_ = v_isSharedCheck_4565_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4561_ = l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1;
                if v_isShared_4560_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4559_, 0);
                    leanh::lean_ctor_set(v___x_4559_, 0, v___x_4561_);
                    v___x_4563_ = v___x_4559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4564_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
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
    mut v_pu_4567_: *mut leanh::LeanObject,
    mut v_b_4568_: *mut leanh::LeanObject,
    mut v_a_4569_: *mut leanh::LeanObject,
    mut v_a_4570_: *mut leanh::LeanObject,
    mut v_a_4571_: *mut leanh::LeanObject,
    mut v_a_4572_: *mut leanh::LeanObject,
    mut v_a_4573_: *mut leanh::LeanObject,
    mut v_a_4574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4575_: u8 = 0;
    let mut v_res_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4575_ = (leanh::lean_unbox(v_pu_4567_) as u8);
    v_res_4576_ = l_Lean_Compiler_LCNF_PP_ppDeclValue(
        v_pu_boxed_4575_,
        v_b_4568_,
        v_a_4569_,
        v_a_4570_,
        v_a_4571_,
        v_a_4572_,
        v_a_4573_,
    );
    leanh::lean_dec(v_a_4573_);
    leanh::lean_dec_ref(v_a_4572_);
    leanh::lean_dec(v_a_4571_);
    leanh::lean_dec_ref(v_a_4570_);
    leanh::lean_dec_ref(v_a_4569_);
    return v_res_4576_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(
    mut v_opts_4577_: *mut leanh::LeanObject,
    mut v_opt_4578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4579_ = leanh::lean_ctor_get(v_opt_4578_, 0);
    v_defValue_4580_ = leanh::lean_ctor_get(v_opt_4578_, 1);
    v_map_4581_ = leanh::lean_ctor_get(v_opts_4577_, 0);
    v___x_4582_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4581_,
            v_name_4579_,
        );
    if leanh::lean_obj_tag(v___x_4582_) == 0 {
        leanh::lean_inc(v_defValue_4580_);
        return v_defValue_4580_;
    } else {
        let mut v_val_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4583_ = leanh::lean_ctor_get(v___x_4582_, 0);
        leanh::lean_inc(v_val_4583_);
        leanh::lean_dec_ref_known(v___x_4582_, 1);
        if leanh::lean_obj_tag(v_val_4583_) == 3 {
            let mut v_v_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_4584_ = leanh::lean_ctor_get(v_val_4583_, 0);
            leanh::lean_inc(v_v_4584_);
            leanh::lean_dec_ref_known(v_val_4583_, 1);
            return v_v_4584_;
        } else {
            leanh::lean_dec(v_val_4583_);
            leanh::lean_inc(v_defValue_4580_);
            return v_defValue_4580_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(
    mut v_opts_4585_: *mut leanh::LeanObject,
    mut v_opt_4586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4587_ =
        l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(v_opts_4585_, v_opt_4586_);
    leanh::lean_dec_ref(v_opt_4586_);
    leanh::lean_dec_ref(v_opts_4585_);
    return v_res_4587_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(
    mut v_o_4591_: *mut leanh::LeanObject,
    mut v_k_4592_: *mut leanh::LeanObject,
    mut v_v_4593_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4595_: u8 = 0;
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4598_: u8 = 0;
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: u8 = 0;
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_4594_ = leanh::lean_ctor_get(v_o_4591_, 0);
                v_hasTrace_4595_ = leanh::lean_ctor_get_uint8(
                    v_o_4591_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4609_ = (!leanh::lean_is_exclusive(v_o_4591_)) as u8;
                if v_isSharedCheck_4609_ == 0 {
                    v___x_4597_ = v_o_4591_;
                    v_isShared_4598_ = v_isSharedCheck_4609_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_4594_);
                    leanh::lean_dec(v_o_4591_);
                    v___x_4597_ = leanh::lean_box(0);
                    v_isShared_4598_ = v_isSharedCheck_4609_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4599_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_4599_, 0 as u32, v_v_4593_);
                leanh::lean_inc(v_k_4592_);
                v___x_4600_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4592_, v___x_4599_, v_map_4594_);
                if v_hasTrace_4595_ == 0 {
                    v___x_4601_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1;
                    v___x_4602_ = l_Lean_Name_isPrefixOf(v___x_4601_, v_k_4592_);
                    leanh::lean_dec(v_k_4592_);
                    if v_isShared_4598_ == 0 {
                        leanh::lean_ctor_set(v___x_4597_, 0, v___x_4600_);
                        v___x_4604_ = v___x_4597_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4605_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4600_);
                        v___x_4604_ = v_reuseFailAlloc_4605_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_4592_);
                    if v_isShared_4598_ == 0 {
                        leanh::lean_ctor_set(v___x_4597_, 0, v___x_4600_);
                        v___x_4607_ = v___x_4597_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4608_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4600_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4608_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_4595_,
                        );
                        v___x_4607_ = v_reuseFailAlloc_4608_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4604_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_o_4610_: *mut leanh::LeanObject,
    mut v_k_4611_: *mut leanh::LeanObject,
    mut v_v_4612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_4613_: u8 = 0;
    let mut v_res_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_4613_ = (leanh::lean_unbox(v_v_4612_) as u8);
    v_res_4614_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(v_o_4610_, v_k_4611_, v_v_boxed_4613_);
    return v_res_4614_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(
    mut v_opts_4615_: *mut leanh::LeanObject,
    mut v_opt_4616_: *mut leanh::LeanObject,
    mut v_val_4617_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4618_ = leanh::lean_ctor_get(v_opt_4616_, 0);
    leanh::lean_inc(v_name_4618_);
    leanh::lean_dec_ref(v_opt_4616_);
    v___x_4619_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(v_opts_4615_, v_name_4618_, v_val_4617_);
    return v___x_4619_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(
    mut v_opts_4620_: *mut leanh::LeanObject,
    mut v_opt_4621_: *mut leanh::LeanObject,
    mut v_val_4622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_4623_: u8 = 0;
    let mut v_res_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_4623_ = (leanh::lean_unbox(v_val_4622_) as u8);
    v_res_4624_ = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(
        v_opts_4620_,
        v_opt_4621_,
        v_val_boxed_4623_,
    );
    return v_res_4624_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4625_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4626_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__0_once),
        _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0,
    );
    v___x_4627_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4627_, 0, v___x_4626_);
    return v___x_4627_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4628_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__1_once),
        _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1,
    );
    v___x_4629_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4629_, 0, v___x_4628_);
    leanh::lean_ctor_set(v___x_4629_, 1, v___x_4628_);
    return v___x_4629_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_run___redArg(
    mut v_x_4630_: *mut leanh::LeanObject,
    mut v_a_4631_: *mut leanh::LeanObject,
    mut v_a_4632_: *mut leanh::LeanObject,
    mut v_a_4633_: *mut leanh::LeanObject,
    mut v_a_4634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: u8 = 0;
    let mut v___y_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4659_: u8 = 0;
    let mut v_inheritedTraceOptions_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: u8 = 0;
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4673_: u8 = 0;
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4677_: u8 = 0;
    let mut v___y_4679_: u8 = 0;
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut v_unused_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4636_ = lean_st_ref_get(v_a_4634_);
                v_options_4637_ = leanh::lean_ctor_get(v_a_4633_, 2);
                v_env_4638_ = leanh::lean_ctor_get(v___x_4636_, 0);
                leanh::lean_inc_ref(v_env_4638_);
                leanh::lean_dec(v___x_4636_);
                v___x_4639_ = l_Lean_pp_sanitizeNames;
                v___x_4640_ = 0;
                leanh::lean_inc_ref(v_options_4637_);
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
                leanh::lean_dec_ref(v_env_4638_);
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
                v_fileName_4648_ = leanh::lean_ctor_get(v___y_4645_, 0);
                v_fileMap_4649_ = leanh::lean_ctor_get(v___y_4645_, 1);
                v_currRecDepth_4650_ = leanh::lean_ctor_get(v___y_4645_, 3);
                v_ref_4651_ = leanh::lean_ctor_get(v___y_4645_, 5);
                v_currNamespace_4652_ = leanh::lean_ctor_get(v___y_4645_, 6);
                v_openDecls_4653_ = leanh::lean_ctor_get(v___y_4645_, 7);
                v_initHeartbeats_4654_ = leanh::lean_ctor_get(v___y_4645_, 8);
                v_maxHeartbeats_4655_ = leanh::lean_ctor_get(v___y_4645_, 9);
                v_quotContext_4656_ = leanh::lean_ctor_get(v___y_4645_, 10);
                v_currMacroScope_4657_ = leanh::lean_ctor_get(v___y_4645_, 11);
                v_cancelTk_x3f_4658_ = leanh::lean_ctor_get(v___y_4645_, 12);
                v_suppressElabErrors_4659_ = leanh::lean_ctor_get_uint8(
                    v___y_4645_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4660_ = leanh::lean_ctor_get(v___y_4645_, 13);
                v___x_4661_ = l_Lean_Compiler_LCNF_getPurity___redArg(v_a_4631_);
                if leanh::lean_obj_tag(v___x_4661_) == 0 {
                    v_a_4662_ = leanh::lean_ctor_get(v___x_4661_, 0);
                    leanh::lean_inc(v_a_4662_);
                    leanh::lean_dec_ref_known(v___x_4661_, 1);
                    v_lctx_4663_ = leanh::lean_ctor_get(v___x_4647_, 0);
                    leanh::lean_inc_ref(v_lctx_4663_);
                    leanh::lean_dec(v___x_4647_);
                    v___x_4664_ = l_Lean_maxRecDepth;
                    v___x_4665_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(
                        v___x_4641_,
                        v___x_4664_,
                    );
                    leanh::lean_inc_ref(v_inheritedTraceOptions_4660_);
                    leanh::lean_inc(v_cancelTk_x3f_4658_);
                    leanh::lean_inc(v_currMacroScope_4657_);
                    leanh::lean_inc(v_quotContext_4656_);
                    leanh::lean_inc(v_maxHeartbeats_4655_);
                    leanh::lean_inc(v_initHeartbeats_4654_);
                    leanh::lean_inc(v_openDecls_4653_);
                    leanh::lean_inc(v_currNamespace_4652_);
                    leanh::lean_inc(v_ref_4651_);
                    leanh::lean_inc(v_currRecDepth_4650_);
                    leanh::lean_inc_ref(v_fileMap_4649_);
                    leanh::lean_inc_ref(v_fileName_4648_);
                    v___x_4666_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v___x_4666_, 0, v_fileName_4648_);
                    leanh::lean_ctor_set(v___x_4666_, 1, v_fileMap_4649_);
                    leanh::lean_ctor_set(v___x_4666_, 2, v___x_4641_);
                    leanh::lean_ctor_set(v___x_4666_, 3, v_currRecDepth_4650_);
                    leanh::lean_ctor_set(v___x_4666_, 4, v___x_4665_);
                    leanh::lean_ctor_set(v___x_4666_, 5, v_ref_4651_);
                    leanh::lean_ctor_set(v___x_4666_, 6, v_currNamespace_4652_);
                    leanh::lean_ctor_set(v___x_4666_, 7, v_openDecls_4653_);
                    leanh::lean_ctor_set(v___x_4666_, 8, v_initHeartbeats_4654_);
                    leanh::lean_ctor_set(v___x_4666_, 9, v_maxHeartbeats_4655_);
                    leanh::lean_ctor_set(v___x_4666_, 10, v_quotContext_4656_);
                    leanh::lean_ctor_set(v___x_4666_, 11, v_currMacroScope_4657_);
                    leanh::lean_ctor_set(v___x_4666_, 12, v_cancelTk_x3f_4658_);
                    leanh::lean_ctor_set(v___x_4666_, 13, v_inheritedTraceOptions_4660_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4666_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v___x_4643_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4666_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_4659_,
                    );
                    v___x_4667_ = (leanh::lean_unbox(v_a_4662_) as u8);
                    leanh::lean_dec(v_a_4662_);
                    v___x_4668_ =
                        l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4663_, v___x_4667_);
                    leanh::lean_dec_ref(v_lctx_4663_);
                    leanh::lean_inc(v___y_4646_);
                    leanh::lean_inc(v_a_4632_);
                    leanh::lean_inc_ref(v_a_4631_);
                    v___x_4669_ = leanh::lean_apply_6(
                        v_x_4630_,
                        v___x_4668_,
                        v_a_4631_,
                        v_a_4632_,
                        v___x_4666_,
                        v___y_4646_,
                        leanh::lean_box(0),
                    );
                    return v___x_4669_;
                } else {
                    leanh::lean_dec(v___x_4647_);
                    leanh::lean_dec_ref(v___x_4641_);
                    leanh::lean_dec_ref(v_x_4630_);
                    v_a_4670_ = leanh::lean_ctor_get(v___x_4661_, 0);
                    v_isSharedCheck_4677_ = (!leanh::lean_is_exclusive(v___x_4661_)) as u8;
                    if v_isSharedCheck_4677_ == 0 {
                        v___x_4672_ = v___x_4661_;
                        v_isShared_4673_ = v_isSharedCheck_4677_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4670_);
                        leanh::lean_dec(v___x_4661_);
                        v___x_4672_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4676_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
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
                    v_env_4681_ = leanh::lean_ctor_get(v___x_4680_, 0);
                    v_nextMacroScope_4682_ = leanh::lean_ctor_get(v___x_4680_, 1);
                    v_ngen_4683_ = leanh::lean_ctor_get(v___x_4680_, 2);
                    v_auxDeclNGen_4684_ = leanh::lean_ctor_get(v___x_4680_, 3);
                    v_traceState_4685_ = leanh::lean_ctor_get(v___x_4680_, 4);
                    v_messages_4686_ = leanh::lean_ctor_get(v___x_4680_, 6);
                    v_infoState_4687_ = leanh::lean_ctor_get(v___x_4680_, 7);
                    v_snapshotTasks_4688_ = leanh::lean_ctor_get(v___x_4680_, 8);
                    v_isSharedCheck_4698_ = (!leanh::lean_is_exclusive(v___x_4680_)) as u8;
                    if v_isSharedCheck_4698_ == 0 {
                        v_unused_4699_ = leanh::lean_ctor_get(v___x_4680_, 5);
                        leanh::lean_dec(v_unused_4699_);
                        v___x_4690_ = v___x_4680_;
                        v_isShared_4691_ = v_isSharedCheck_4698_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_4688_);
                        leanh::lean_inc(v_infoState_4687_);
                        leanh::lean_inc(v_messages_4686_);
                        leanh::lean_inc(v_traceState_4685_);
                        leanh::lean_inc(v_auxDeclNGen_4684_);
                        leanh::lean_inc(v_ngen_4683_);
                        leanh::lean_inc(v_nextMacroScope_4682_);
                        leanh::lean_inc(v_env_4681_);
                        leanh::lean_dec(v___x_4680_);
                        v___x_4690_ = leanh::lean_box(0);
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
                v___x_4693_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_PP_run___redArg___closed__2_once),
                    _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2,
                );
                if v_isShared_4691_ == 0 {
                    leanh::lean_ctor_set(v___x_4690_, 5, v___x_4693_);
                    leanh::lean_ctor_set(v___x_4690_, 0, v___x_4692_);
                    v___x_4695_ = v___x_4690_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4697_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 1, v_nextMacroScope_4682_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 2, v_ngen_4683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 3, v_auxDeclNGen_4684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 4, v_traceState_4685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 5, v___x_4693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 6, v_messages_4686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 7, v_infoState_4687_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 8, v_snapshotTasks_4688_);
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
    mut v_x_4701_: *mut leanh::LeanObject,
    mut v_a_4702_: *mut leanh::LeanObject,
    mut v_a_4703_: *mut leanh::LeanObject,
    mut v_a_4704_: *mut leanh::LeanObject,
    mut v_a_4705_: *mut leanh::LeanObject,
    mut v_a_4706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4707_ =
        l_Lean_Compiler_LCNF_PP_run___redArg(v_x_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
    leanh::lean_dec(v_a_4705_);
    leanh::lean_dec_ref(v_a_4704_);
    leanh::lean_dec(v_a_4703_);
    leanh::lean_dec_ref(v_a_4702_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_run(
    mut v_00_u03b1_4708_: *mut leanh::LeanObject,
    mut v_x_4709_: *mut leanh::LeanObject,
    mut v_a_4710_: *mut leanh::LeanObject,
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
    mut v_a_4713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4715_ =
        l_Lean_Compiler_LCNF_PP_run___redArg(v_x_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_);
    return v___x_4715_;
}
pub unsafe fn l_Lean_Compiler_LCNF_PP_run___boxed(
    mut v_00_u03b1_4716_: *mut leanh::LeanObject,
    mut v_x_4717_: *mut leanh::LeanObject,
    mut v_a_4718_: *mut leanh::LeanObject,
    mut v_a_4719_: *mut leanh::LeanObject,
    mut v_a_4720_: *mut leanh::LeanObject,
    mut v_a_4721_: *mut leanh::LeanObject,
    mut v_a_4722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4723_ = l_Lean_Compiler_LCNF_PP_run(
        v_00_u03b1_4716_,
        v_x_4717_,
        v_a_4718_,
        v_a_4719_,
        v_a_4720_,
        v_a_4721_,
    );
    leanh::lean_dec(v_a_4721_);
    leanh::lean_dec_ref(v_a_4720_);
    leanh::lean_dec(v_a_4719_);
    leanh::lean_dec_ref(v_a_4718_);
    return v_res_4723_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode(
    mut v_pu_4724_: u8,
    mut v_code_4725_: *mut leanh::LeanObject,
    mut v_a_4726_: *mut leanh::LeanObject,
    mut v_a_4727_: *mut leanh::LeanObject,
    mut v_a_4728_: *mut leanh::LeanObject,
    mut v_a_4729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4731_ = leanh::lean_box((v_pu_4724_) as usize);
    v___x_4732_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PP_ppCode___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    leanh::lean_closure_set(v___x_4732_, 0, v___x_4731_);
    leanh::lean_closure_set(v___x_4732_, 1, v_code_4725_);
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
    mut v_pu_4734_: *mut leanh::LeanObject,
    mut v_code_4735_: *mut leanh::LeanObject,
    mut v_a_4736_: *mut leanh::LeanObject,
    mut v_a_4737_: *mut leanh::LeanObject,
    mut v_a_4738_: *mut leanh::LeanObject,
    mut v_a_4739_: *mut leanh::LeanObject,
    mut v_a_4740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4741_: u8 = 0;
    let mut v_res_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4741_ = (leanh::lean_unbox(v_pu_4734_) as u8);
    v_res_4742_ = l_Lean_Compiler_LCNF_ppCode(
        v_pu_boxed_4741_,
        v_code_4735_,
        v_a_4736_,
        v_a_4737_,
        v_a_4738_,
        v_a_4739_,
    );
    leanh::lean_dec(v_a_4739_);
    leanh::lean_dec_ref(v_a_4738_);
    leanh::lean_dec(v_a_4737_);
    leanh::lean_dec_ref(v_a_4736_);
    return v_res_4742_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppLetValue(
    mut v_pu_4743_: u8,
    mut v_e_4744_: *mut leanh::LeanObject,
    mut v_a_4745_: *mut leanh::LeanObject,
    mut v_a_4746_: *mut leanh::LeanObject,
    mut v_a_4747_: *mut leanh::LeanObject,
    mut v_a_4748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4750_ = leanh::lean_box((v_pu_4743_) as usize);
    v___x_4751_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_PP_ppLetValue___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    leanh::lean_closure_set(v___x_4751_, 0, v___x_4750_);
    leanh::lean_closure_set(v___x_4751_, 1, v_e_4744_);
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
    mut v_pu_4753_: *mut leanh::LeanObject,
    mut v_e_4754_: *mut leanh::LeanObject,
    mut v_a_4755_: *mut leanh::LeanObject,
    mut v_a_4756_: *mut leanh::LeanObject,
    mut v_a_4757_: *mut leanh::LeanObject,
    mut v_a_4758_: *mut leanh::LeanObject,
    mut v_a_4759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4760_: u8 = 0;
    let mut v_res_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4760_ = (leanh::lean_unbox(v_pu_4753_) as u8);
    v_res_4761_ = l_Lean_Compiler_LCNF_ppLetValue(
        v_pu_boxed_4760_,
        v_e_4754_,
        v_a_4755_,
        v_a_4756_,
        v_a_4757_,
        v_a_4758_,
    );
    leanh::lean_dec(v_a_4758_);
    leanh::lean_dec_ref(v_a_4757_);
    leanh::lean_dec(v_a_4756_);
    leanh::lean_dec_ref(v_a_4755_);
    return v_res_4761_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl___lam__0(
    mut v_pu_4765_: u8,
    mut v_params_4766_: *mut leanh::LeanObject,
    mut v_type_4767_: *mut leanh::LeanObject,
    mut v_value_4768_: *mut leanh::LeanObject,
    mut v_name_4769_: *mut leanh::LeanObject,
    mut v___y_4770_: *mut leanh::LeanObject,
    mut v___y_4771_: *mut leanh::LeanObject,
    mut v___y_4772_: *mut leanh::LeanObject,
    mut v___y_4773_: *mut leanh::LeanObject,
    mut v___y_4774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4784_: u8 = 0;
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4789_: u8 = 0;
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut v_a_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4813_: u8 = 0;
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_4776_) == 0 {
                    v_a_4777_ = leanh::lean_ctor_get(v___x_4776_, 0);
                    leanh::lean_inc(v_a_4777_);
                    leanh::lean_dec_ref_known(v___x_4776_, 1);
                    v___x_4778_ = l_Lean_Compiler_LCNF_PP_getFunType(
                        v_pu_4765_,
                        v_params_4766_,
                        v_type_4767_,
                        v___y_4773_,
                        v___y_4774_,
                    );
                    if leanh::lean_obj_tag(v___x_4778_) == 0 {
                        v_a_4779_ = leanh::lean_ctor_get(v___x_4778_, 0);
                        leanh::lean_inc(v_a_4779_);
                        leanh::lean_dec_ref_known(v___x_4778_, 1);
                        v___x_4780_ = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(
                            v_a_4779_,
                            v___y_4770_,
                            v___y_4773_,
                            v___y_4774_,
                        );
                        if leanh::lean_obj_tag(v___x_4780_) == 0 {
                            v_a_4781_ = leanh::lean_ctor_get(v___x_4780_, 0);
                            v_isSharedCheck_4809_ =
                                (!leanh::lean_is_exclusive(v___x_4780_)) as u8;
                            if v_isSharedCheck_4809_ == 0 {
                                v___x_4783_ = v___x_4780_;
                                v_isShared_4784_ = v_isSharedCheck_4809_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4781_);
                                leanh::lean_dec(v___x_4780_);
                                v___x_4783_ = leanh::lean_box(0);
                                v_isShared_4784_ = v_isSharedCheck_4809_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4777_);
                            leanh::lean_dec(v_name_4769_);
                            leanh::lean_dec_ref(v_value_4768_);
                            return v___x_4780_;
                        }
                    } else {
                        leanh::lean_dec(v_a_4777_);
                        leanh::lean_dec(v_name_4769_);
                        leanh::lean_dec_ref(v_value_4768_);
                        v_a_4810_ = leanh::lean_ctor_get(v___x_4778_, 0);
                        v_isSharedCheck_4817_ =
                            (!leanh::lean_is_exclusive(v___x_4778_)) as u8;
                        if v_isSharedCheck_4817_ == 0 {
                            v___x_4812_ = v___x_4778_;
                            v_isShared_4813_ = v_isSharedCheck_4817_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4810_);
                            leanh::lean_dec(v___x_4778_);
                            v___x_4812_ = leanh::lean_box(0);
                            v_isShared_4813_ = v_isSharedCheck_4817_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_name_4769_);
                    leanh::lean_dec_ref(v_value_4768_);
                    leanh::lean_dec_ref(v_type_4767_);
                    leanh::lean_dec_ref(v_params_4766_);
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
                if leanh::lean_obj_tag(v___x_4785_) == 0 {
                    v_a_4786_ = leanh::lean_ctor_get(v___x_4785_, 0);
                    v_isSharedCheck_4808_ = (!leanh::lean_is_exclusive(v___x_4785_)) as u8;
                    if v_isSharedCheck_4808_ == 0 {
                        v___x_4788_ = v___x_4785_;
                        v_isShared_4789_ = v_isSharedCheck_4808_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4786_);
                        leanh::lean_dec(v___x_4785_);
                        v___x_4788_ = leanh::lean_box(0);
                        v_isShared_4789_ = v_isSharedCheck_4808_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4783_);
                    leanh::lean_dec(v_a_4781_);
                    leanh::lean_dec(v_a_4777_);
                    leanh::lean_dec(v_name_4769_);
                    return v___x_4785_;
                }
            }
            2 => {
                v___x_4790_ = l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1;
                v___x_4791_ = 1;
                v___x_4792_ = l_Lean_Name_toString(v_name_4769_, v___x_4791_);
                if v_isShared_4784_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4783_, 3);
                    leanh::lean_ctor_set(v___x_4783_, 0, v___x_4792_);
                    v___x_4794_ = v___x_4783_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4807_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4792_);
                    v___x_4794_ = v_reuseFailAlloc_4807_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4795_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4795_, 0, v___x_4790_);
                leanh::lean_ctor_set(v___x_4795_, 1, v___x_4794_);
                v___x_4796_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4796_, 0, v___x_4795_);
                leanh::lean_ctor_set(v___x_4796_, 1, v_a_4777_);
                v___x_4797_ = l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1;
                v___x_4798_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4798_, 0, v___x_4796_);
                leanh::lean_ctor_set(v___x_4798_, 1, v___x_4797_);
                v___x_4799_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4799_, 0, v___x_4798_);
                leanh::lean_ctor_set(v___x_4799_, 1, v_a_4781_);
                v___x_4800_ = l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1;
                v___x_4801_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4801_, 0, v___x_4799_);
                leanh::lean_ctor_set(v___x_4801_, 1, v___x_4800_);
                v___x_4802_ = l_Std_Format_indentD(v_a_4786_);
                v___x_4803_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4803_, 0, v___x_4801_);
                leanh::lean_ctor_set(v___x_4803_, 1, v___x_4802_);
                if v_isShared_4789_ == 0 {
                    leanh::lean_ctor_set(v___x_4788_, 0, v___x_4803_);
                    v___x_4805_ = v___x_4788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4803_);
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
                    v_reuseFailAlloc_4816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
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
    mut v_pu_4818_: *mut leanh::LeanObject,
    mut v_params_4819_: *mut leanh::LeanObject,
    mut v_type_4820_: *mut leanh::LeanObject,
    mut v_value_4821_: *mut leanh::LeanObject,
    mut v_name_4822_: *mut leanh::LeanObject,
    mut v___y_4823_: *mut leanh::LeanObject,
    mut v___y_4824_: *mut leanh::LeanObject,
    mut v___y_4825_: *mut leanh::LeanObject,
    mut v___y_4826_: *mut leanh::LeanObject,
    mut v___y_4827_: *mut leanh::LeanObject,
    mut v___y_4828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4829_: u8 = 0;
    let mut v_res_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4829_ = (leanh::lean_unbox(v_pu_4818_) as u8);
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
    leanh::lean_dec(v___y_4827_);
    leanh::lean_dec_ref(v___y_4826_);
    leanh::lean_dec(v___y_4825_);
    leanh::lean_dec_ref(v___y_4824_);
    leanh::lean_dec_ref(v___y_4823_);
    return v_res_4830_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl(
    mut v_pu_4831_: u8,
    mut v_decl_4832_: *mut leanh::LeanObject,
    mut v_a_4833_: *mut leanh::LeanObject,
    mut v_a_4834_: *mut leanh::LeanObject,
    mut v_a_4835_: *mut leanh::LeanObject,
    mut v_a_4836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSignature_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toSignature_4838_ = leanh::lean_ctor_get(v_decl_4832_, 0);
    leanh::lean_inc_ref(v_toSignature_4838_);
    v_value_4839_ = leanh::lean_ctor_get(v_decl_4832_, 1);
    leanh::lean_inc_ref(v_value_4839_);
    leanh::lean_dec_ref(v_decl_4832_);
    v_name_4840_ = leanh::lean_ctor_get(v_toSignature_4838_, 0);
    leanh::lean_inc(v_name_4840_);
    v_type_4841_ = leanh::lean_ctor_get(v_toSignature_4838_, 2);
    leanh::lean_inc_ref(v_type_4841_);
    v_params_4842_ = leanh::lean_ctor_get(v_toSignature_4838_, 3);
    leanh::lean_inc_ref(v_params_4842_);
    leanh::lean_dec_ref(v_toSignature_4838_);
    v___x_4843_ = leanh::lean_box((v_pu_4831_) as usize);
    v___f_4844_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed as *mut core::ffi::c_void,
        11,
        5,
    );
    leanh::lean_closure_set(v___f_4844_, 0, v___x_4843_);
    leanh::lean_closure_set(v___f_4844_, 1, v_params_4842_);
    leanh::lean_closure_set(v___f_4844_, 2, v_type_4841_);
    leanh::lean_closure_set(v___f_4844_, 3, v_value_4839_);
    leanh::lean_closure_set(v___f_4844_, 4, v_name_4840_);
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
    mut v_pu_4846_: *mut leanh::LeanObject,
    mut v_decl_4847_: *mut leanh::LeanObject,
    mut v_a_4848_: *mut leanh::LeanObject,
    mut v_a_4849_: *mut leanh::LeanObject,
    mut v_a_4850_: *mut leanh::LeanObject,
    mut v_a_4851_: *mut leanh::LeanObject,
    mut v_a_4852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4853_: u8 = 0;
    let mut v_res_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4853_ = (leanh::lean_unbox(v_pu_4846_) as u8);
    v_res_4854_ = l_Lean_Compiler_LCNF_ppDecl(
        v_pu_boxed_4853_,
        v_decl_4847_,
        v_a_4848_,
        v_a_4849_,
        v_a_4850_,
        v_a_4851_,
    );
    leanh::lean_dec(v_a_4851_);
    leanh::lean_dec_ref(v_a_4850_);
    leanh::lean_dec(v_a_4849_);
    leanh::lean_dec_ref(v_a_4848_);
    return v_res_4854_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppFunDecl___lam__0(
    mut v_pu_4855_: u8,
    mut v_decl_4856_: *mut leanh::LeanObject,
    mut v___y_4857_: *mut leanh::LeanObject,
    mut v___y_4858_: *mut leanh::LeanObject,
    mut v___y_4859_: *mut leanh::LeanObject,
    mut v___y_4860_: *mut leanh::LeanObject,
    mut v___y_4861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_4863_) == 0 {
                    v_a_4864_ = leanh::lean_ctor_get(v___x_4863_, 0);
                    v_isSharedCheck_4873_ = (!leanh::lean_is_exclusive(v___x_4863_)) as u8;
                    if v_isSharedCheck_4873_ == 0 {
                        v___x_4866_ = v___x_4863_;
                        v_isShared_4867_ = v_isSharedCheck_4873_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4864_);
                        leanh::lean_dec(v___x_4863_);
                        v___x_4866_ = leanh::lean_box(0);
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
                v___x_4869_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4869_, 0, v___x_4868_);
                leanh::lean_ctor_set(v___x_4869_, 1, v_a_4864_);
                if v_isShared_4867_ == 0 {
                    leanh::lean_ctor_set(v___x_4866_, 0, v___x_4869_);
                    v___x_4871_ = v___x_4866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4872_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4869_);
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
    mut v_pu_4874_: *mut leanh::LeanObject,
    mut v_decl_4875_: *mut leanh::LeanObject,
    mut v___y_4876_: *mut leanh::LeanObject,
    mut v___y_4877_: *mut leanh::LeanObject,
    mut v___y_4878_: *mut leanh::LeanObject,
    mut v___y_4879_: *mut leanh::LeanObject,
    mut v___y_4880_: *mut leanh::LeanObject,
    mut v___y_4881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4882_: u8 = 0;
    let mut v_res_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4882_ = (leanh::lean_unbox(v_pu_4874_) as u8);
    v_res_4883_ = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(
        v_pu_boxed_4882_,
        v_decl_4875_,
        v___y_4876_,
        v___y_4877_,
        v___y_4878_,
        v___y_4879_,
        v___y_4880_,
    );
    leanh::lean_dec(v___y_4880_);
    leanh::lean_dec_ref(v___y_4879_);
    leanh::lean_dec(v___y_4878_);
    leanh::lean_dec_ref(v___y_4877_);
    leanh::lean_dec_ref(v___y_4876_);
    return v_res_4883_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppFunDecl(
    mut v_pu_4884_: u8,
    mut v_decl_4885_: *mut leanh::LeanObject,
    mut v_a_4886_: *mut leanh::LeanObject,
    mut v_a_4887_: *mut leanh::LeanObject,
    mut v_a_4888_: *mut leanh::LeanObject,
    mut v_a_4889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4891_ = leanh::lean_box((v_pu_4884_) as usize);
    v___f_4892_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    leanh::lean_closure_set(v___f_4892_, 0, v___x_4891_);
    leanh::lean_closure_set(v___f_4892_, 1, v_decl_4885_);
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
    mut v_pu_4894_: *mut leanh::LeanObject,
    mut v_decl_4895_: *mut leanh::LeanObject,
    mut v_a_4896_: *mut leanh::LeanObject,
    mut v_a_4897_: *mut leanh::LeanObject,
    mut v_a_4898_: *mut leanh::LeanObject,
    mut v_a_4899_: *mut leanh::LeanObject,
    mut v_a_4900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_4901_: u8 = 0;
    let mut v_res_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4901_ = (leanh::lean_unbox(v_pu_4894_) as u8);
    v_res_4902_ = l_Lean_Compiler_LCNF_ppFunDecl(
        v_pu_boxed_4901_,
        v_decl_4895_,
        v_a_4896_,
        v_a_4897_,
        v_a_4898_,
        v_a_4899_,
    );
    leanh::lean_dec(v_a_4899_);
    leanh::lean_dec_ref(v_a_4898_);
    leanh::lean_dec(v_a_4897_);
    leanh::lean_dec_ref(v_a_4896_);
    return v_res_4902_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(
    mut v_a_4903_: *mut leanh::LeanObject,
    mut v_val_4904_: *mut leanh::LeanObject,
    mut v_a_x3f_4905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4907_ = lean_st_ref_set(v_a_4903_, v_val_4904_);
    v___x_4908_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4908_, 0, v___x_4907_);
    return v___x_4908_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(
    mut v_a_4909_: *mut leanh::LeanObject,
    mut v_val_4910_: *mut leanh::LeanObject,
    mut v_a_x3f_4911_: *mut leanh::LeanObject,
    mut v___y_4912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4913_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(
        v_a_4909_,
        v_val_4910_,
        v_a_x3f_4911_,
    );
    leanh::lean_dec(v_a_x3f_4911_);
    leanh::lean_dec(v_a_4909_);
    return v_res_4913_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4914_ = leanh::lean_box(0);
    v___x_4915_ = leanh::lean_unsigned_to_nat(16);
    v___x_4916_ = lean_mk_array(v___x_4915_, v___x_4914_);
    return v___x_4916_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4917_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0,
    );
    v___x_4918_ = leanh::lean_unsigned_to_nat(0);
    v___x_4919_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4919_, 0, v___x_4918_);
    leanh::lean_ctor_set(v___x_4919_, 1, v___x_4917_);
    return v___x_4919_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1,
    );
    v___x_4921_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_4921_, 0, v___x_4920_);
    leanh::lean_ctor_set(v___x_4921_, 1, v___x_4920_);
    leanh::lean_ctor_set(v___x_4921_, 2, v___x_4920_);
    leanh::lean_ctor_set(v___x_4921_, 3, v___x_4920_);
    leanh::lean_ctor_set(v___x_4921_, 4, v___x_4920_);
    leanh::lean_ctor_set(v___x_4921_, 5, v___x_4920_);
    return v___x_4921_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4922_ = leanh::lean_unsigned_to_nat(1);
    v___x_4923_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2,
    );
    v___x_4924_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4924_, 0, v___x_4923_);
    leanh::lean_ctor_set(v___x_4924_, 1, v___x_4922_);
    return v___x_4924_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
    mut v_phase_4925_: u8,
    mut v_x_4926_: *mut leanh::LeanObject,
    mut v_a_4927_: *mut leanh::LeanObject,
    mut v_a_4928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4946_: u8 = 0;
    let mut v_unused_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_a_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4955_: u8 = 0;
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4959_: u8 = 0;
    let mut v_unused_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4930_ = lean_st_ref_get(v_a_4928_);
                v___x_4931_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3_once), _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3);
                v_r_4932_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(
                    v_x_4926_,
                    v___x_4931_,
                    v_phase_4925_,
                    v_a_4927_,
                    v_a_4928_,
                );
                if leanh::lean_obj_tag(v_r_4932_) == 0 {
                    v_a_4933_ = leanh::lean_ctor_get(v_r_4932_, 0);
                    v_isSharedCheck_4949_ = (!leanh::lean_is_exclusive(v_r_4932_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v___x_4935_ = v_r_4932_;
                        v_isShared_4936_ = v_isSharedCheck_4949_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4933_);
                        leanh::lean_dec(v_r_4932_);
                        v___x_4935_ = leanh::lean_box(0);
                        v_isShared_4936_ = v_isSharedCheck_4949_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4950_ = leanh::lean_ctor_get(v_r_4932_, 0);
                    leanh::lean_inc(v_a_4950_);
                    leanh::lean_dec_ref_known(v_r_4932_, 1);
                    v___x_4951_ = leanh::lean_box(0);
                    v___x_4952_ =
                        l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(
                            v_a_4928_,
                            v___x_4930_,
                            v___x_4951_,
                        );
                    v_isSharedCheck_4959_ = (!leanh::lean_is_exclusive(v___x_4952_)) as u8;
                    if v_isSharedCheck_4959_ == 0 {
                        v_unused_4960_ = leanh::lean_ctor_get(v___x_4952_, 0);
                        leanh::lean_dec(v_unused_4960_);
                        v___x_4954_ = v___x_4952_;
                        v_isShared_4955_ = v_isSharedCheck_4959_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4952_);
                        v___x_4954_ = leanh::lean_box(0);
                        v_isShared_4955_ = v_isSharedCheck_4959_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_4933_);
                if v_isShared_4936_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4935_, 1);
                    v___x_4938_ = v___x_4935_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4933_);
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
                leanh::lean_dec_ref(v___x_4938_);
                v_isSharedCheck_4946_ = (!leanh::lean_is_exclusive(v___x_4939_)) as u8;
                if v_isSharedCheck_4946_ == 0 {
                    v_unused_4947_ = leanh::lean_ctor_get(v___x_4939_, 0);
                    leanh::lean_dec(v_unused_4947_);
                    v___x_4941_ = v___x_4939_;
                    v_isShared_4942_ = v_isSharedCheck_4946_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4939_);
                    v___x_4941_ = leanh::lean_box(0);
                    v_isShared_4942_ = v_isSharedCheck_4946_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4942_ == 0 {
                    leanh::lean_ctor_set(v___x_4941_, 0, v_a_4933_);
                    v___x_4944_ = v___x_4941_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4945_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4933_);
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
                    leanh::lean_ctor_set_tag(v___x_4954_, 1);
                    leanh::lean_ctor_set(v___x_4954_, 0, v_a_4950_);
                    v___x_4957_ = v___x_4954_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4958_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4950_);
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
    mut v_phase_4961_: *mut leanh::LeanObject,
    mut v_x_4962_: *mut leanh::LeanObject,
    mut v_a_4963_: *mut leanh::LeanObject,
    mut v_a_4964_: *mut leanh::LeanObject,
    mut v_a_4965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_4966_: u8 = 0;
    let mut v_res_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_4966_ = (leanh::lean_unbox(v_phase_4961_) as u8);
    v_res_4967_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
        v_phase_boxed_4966_,
        v_x_4962_,
        v_a_4963_,
        v_a_4964_,
    );
    leanh::lean_dec(v_a_4964_);
    leanh::lean_dec_ref(v_a_4963_);
    return v_res_4967_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(
    mut v_00_u03b1_4968_: *mut leanh::LeanObject,
    mut v_phase_4969_: u8,
    mut v_x_4970_: *mut leanh::LeanObject,
    mut v_a_4971_: *mut leanh::LeanObject,
    mut v_a_4972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4974_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
        v_phase_4969_,
        v_x_4970_,
        v_a_4971_,
        v_a_4972_,
    );
    return v___x_4974_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(
    mut v_00_u03b1_4975_: *mut leanh::LeanObject,
    mut v_phase_4976_: *mut leanh::LeanObject,
    mut v_x_4977_: *mut leanh::LeanObject,
    mut v_a_4978_: *mut leanh::LeanObject,
    mut v_a_4979_: *mut leanh::LeanObject,
    mut v_a_4980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_4981_: u8 = 0;
    let mut v_res_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_4981_ = (leanh::lean_unbox(v_phase_4976_) as u8);
    v_res_4982_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(
        v_00_u03b1_4975_,
        v_phase_boxed_4981_,
        v_x_4977_,
        v_a_4978_,
        v_a_4979_,
    );
    leanh::lean_dec(v_a_4979_);
    leanh::lean_dec_ref(v_a_4978_);
    return v_res_4982_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(
    mut v_pu_4983_: u8,
    mut v_decl_4984_: *mut leanh::LeanObject,
    mut v___x_4985_: *mut leanh::LeanObject,
    mut v___x_4986_: u8,
    mut v___y_4987_: *mut leanh::LeanObject,
    mut v___y_4988_: *mut leanh::LeanObject,
    mut v___y_4989_: *mut leanh::LeanObject,
    mut v___y_4990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_4992_) == 0 {
                    v_a_4993_ = leanh::lean_ctor_get(v___x_4992_, 0);
                    leanh::lean_inc(v_a_4993_);
                    leanh::lean_dec_ref_known(v___x_4992_, 1);
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
                    v_a_4995_ = leanh::lean_ctor_get(v___x_4992_, 0);
                    v_isSharedCheck_5002_ = (!leanh::lean_is_exclusive(v___x_4992_)) as u8;
                    if v_isSharedCheck_5002_ == 0 {
                        v___x_4997_ = v___x_4992_;
                        v_isShared_4998_ = v_isSharedCheck_5002_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4995_);
                        leanh::lean_dec(v___x_4992_);
                        v___x_4997_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
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
    mut v_pu_5003_: *mut leanh::LeanObject,
    mut v_decl_5004_: *mut leanh::LeanObject,
    mut v___x_5005_: *mut leanh::LeanObject,
    mut v___x_5006_: *mut leanh::LeanObject,
    mut v___y_5007_: *mut leanh::LeanObject,
    mut v___y_5008_: *mut leanh::LeanObject,
    mut v___y_5009_: *mut leanh::LeanObject,
    mut v___y_5010_: *mut leanh::LeanObject,
    mut v___y_5011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5012_: u8 = 0;
    let mut v___x_99__boxed_5013_: u8 = 0;
    let mut v_res_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5012_ = (leanh::lean_unbox(v_pu_5003_) as u8);
    v___x_99__boxed_5013_ = (leanh::lean_unbox(v___x_5006_) as u8);
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
    leanh::lean_dec(v___y_5010_);
    leanh::lean_dec_ref(v___y_5009_);
    leanh::lean_dec(v___y_5008_);
    leanh::lean_dec_ref(v___y_5007_);
    return v_res_5014_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl_x27(
    mut v_pu_5015_: u8,
    mut v_decl_5016_: *mut leanh::LeanObject,
    mut v_phase_5017_: u8,
    mut v_a_5018_: *mut leanh::LeanObject,
    mut v_a_5019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: u8 = 0;
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5021_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1,
    );
    v___x_5022_ = 0;
    v___x_5023_ = leanh::lean_box((v_pu_5015_) as usize);
    v___x_5024_ = leanh::lean_box((v___x_5022_) as usize);
    v___f_5025_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_5025_, 0, v___x_5023_);
    leanh::lean_closure_set(v___f_5025_, 1, v_decl_5016_);
    leanh::lean_closure_set(v___f_5025_, 2, v___x_5021_);
    leanh::lean_closure_set(v___f_5025_, 3, v___x_5024_);
    v___x_5026_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
        v_phase_5017_,
        v___f_5025_,
        v_a_5018_,
        v_a_5019_,
    );
    return v___x_5026_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppDecl_x27___boxed(
    mut v_pu_5027_: *mut leanh::LeanObject,
    mut v_decl_5028_: *mut leanh::LeanObject,
    mut v_phase_5029_: *mut leanh::LeanObject,
    mut v_a_5030_: *mut leanh::LeanObject,
    mut v_a_5031_: *mut leanh::LeanObject,
    mut v_a_5032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5033_: u8 = 0;
    let mut v_phase_boxed_5034_: u8 = 0;
    let mut v_res_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5033_ = (leanh::lean_unbox(v_pu_5027_) as u8);
    v_phase_boxed_5034_ = (leanh::lean_unbox(v_phase_5029_) as u8);
    v_res_5035_ = l_Lean_Compiler_LCNF_ppDecl_x27(
        v_pu_boxed_5033_,
        v_decl_5028_,
        v_phase_boxed_5034_,
        v_a_5030_,
        v_a_5031_,
    );
    leanh::lean_dec(v_a_5031_);
    leanh::lean_dec_ref(v_a_5030_);
    return v_res_5035_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode_x27___lam__0(
    mut v_pu_5036_: u8,
    mut v_code_5037_: *mut leanh::LeanObject,
    mut v___x_5038_: *mut leanh::LeanObject,
    mut v___x_5039_: u8,
    mut v___y_5040_: *mut leanh::LeanObject,
    mut v___y_5041_: *mut leanh::LeanObject,
    mut v___y_5042_: *mut leanh::LeanObject,
    mut v___y_5043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_5045_) == 0 {
                    v_a_5046_ = leanh::lean_ctor_get(v___x_5045_, 0);
                    leanh::lean_inc(v_a_5046_);
                    leanh::lean_dec_ref_known(v___x_5045_, 1);
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
                    v_a_5048_ = leanh::lean_ctor_get(v___x_5045_, 0);
                    v_isSharedCheck_5055_ = (!leanh::lean_is_exclusive(v___x_5045_)) as u8;
                    if v_isSharedCheck_5055_ == 0 {
                        v___x_5050_ = v___x_5045_;
                        v_isShared_5051_ = v_isSharedCheck_5055_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5048_);
                        leanh::lean_dec(v___x_5045_);
                        v___x_5050_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
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
    mut v_pu_5056_: *mut leanh::LeanObject,
    mut v_code_5057_: *mut leanh::LeanObject,
    mut v___x_5058_: *mut leanh::LeanObject,
    mut v___x_5059_: *mut leanh::LeanObject,
    mut v___y_5060_: *mut leanh::LeanObject,
    mut v___y_5061_: *mut leanh::LeanObject,
    mut v___y_5062_: *mut leanh::LeanObject,
    mut v___y_5063_: *mut leanh::LeanObject,
    mut v___y_5064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5065_: u8 = 0;
    let mut v___x_99__boxed_5066_: u8 = 0;
    let mut v_res_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5065_ = (leanh::lean_unbox(v_pu_5056_) as u8);
    v___x_99__boxed_5066_ = (leanh::lean_unbox(v___x_5059_) as u8);
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
    leanh::lean_dec(v___y_5063_);
    leanh::lean_dec_ref(v___y_5062_);
    leanh::lean_dec(v___y_5061_);
    leanh::lean_dec_ref(v___y_5060_);
    return v_res_5067_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode_x27(
    mut v_pu_5068_: u8,
    mut v_code_5069_: *mut leanh::LeanObject,
    mut v_phase_5070_: u8,
    mut v_a_5071_: *mut leanh::LeanObject,
    mut v_a_5072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: u8 = 0;
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5074_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1,
    );
    v___x_5075_ = 0;
    v___x_5076_ = leanh::lean_box((v_pu_5068_) as usize);
    v___x_5077_ = leanh::lean_box((v___x_5075_) as usize);
    v___f_5078_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_5078_, 0, v___x_5076_);
    leanh::lean_closure_set(v___f_5078_, 1, v_code_5069_);
    leanh::lean_closure_set(v___f_5078_, 2, v___x_5074_);
    leanh::lean_closure_set(v___f_5078_, 3, v___x_5077_);
    v___x_5079_ = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(
        v_phase_5070_,
        v___f_5078_,
        v_a_5071_,
        v_a_5072_,
    );
    return v___x_5079_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ppCode_x27___boxed(
    mut v_pu_5080_: *mut leanh::LeanObject,
    mut v_code_5081_: *mut leanh::LeanObject,
    mut v_phase_5082_: *mut leanh::LeanObject,
    mut v_a_5083_: *mut leanh::LeanObject,
    mut v_a_5084_: *mut leanh::LeanObject,
    mut v_a_5085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5086_: u8 = 0;
    let mut v_phase_boxed_5087_: u8 = 0;
    let mut v_res_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5086_ = (leanh::lean_unbox(v_pu_5080_) as u8);
    v_phase_boxed_5087_ = (leanh::lean_unbox(v_phase_5082_) as u8);
    v_res_5088_ = l_Lean_Compiler_LCNF_ppCode_x27(
        v_pu_boxed_5086_,
        v_code_5081_,
        v_phase_boxed_5087_,
        v_a_5083_,
        v_a_5084_,
    );
    leanh::lean_dec(v_a_5084_);
    leanh::lean_dec_ref(v_a_5083_);
    return v_res_5088_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_PrettyPrinter(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_PrettyPrinter(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
}
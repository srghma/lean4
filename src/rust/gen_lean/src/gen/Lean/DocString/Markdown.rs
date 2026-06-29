// Lean compiler output
// Module: Lean.DocString.Markdown
// Imports: Lean.DocString.Types Init.Data.String.TakeDrop Init.Data.String.Search Init.Data.String.Length Init.Data.ToString.Macro Init.While
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Nat::Basic::l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Prelude::l_Array_extract___redArg;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::DocString::Types::{
    initialize_Lean_DocString_Types, l_Lean_Doc_Inline_empty,
    runtime_initialize_Lean_DocString_Types,
};
use crate::ffi::{
    lean_array_pop, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::ffi::lean_string_push;
use crate::ffi::lean_string_append;
use crate::ffi::lean_string_memcmp;
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_mk,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint32_dec_le, lean_usize_dec_eq,
};
pub static l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_MarkdownM_instInhabitedInlineCtx: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0_value:
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
    m_data: [91, 94, 0],
};
static mut l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1_value:
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
    m_data: [93, 58, 0],
};
static mut l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_MarkdownM_run_x27___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Doc_MarkdownM_run_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_MarkdownM_run_x27___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_MarkdownM_run_x27___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [10, 0],
    };
static mut l_Lean_Doc_MarkdownM_run_x27___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_MarkdownM_run_x27___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_MarkdownM_run_x27___closed__2_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [10, 10, 0],
    };
static mut l_Lean_Doc_MarkdownM_run_x27___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_MarkdownM_run_x27___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_joinBlocks___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Doc_joinBlocks___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_joinBlocks___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0_value:
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
    m_data: [96, 0],
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_value:
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
    m_data: [226, 128, 139, 0],
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Doc_instMarkdownInlineEmpty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_instMarkdownInlineEmpty: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instMarkdownInlineEmpty___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Doc_instMarkdownBlockEmpty___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Doc_instMarkdownBlockEmpty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Doc_instMarkdownBlockEmpty___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [42, 95, 96, 60, 91, 93, 123, 125, 40, 41, 35, 0],
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [62, 32, 45, 43, 46, 32, 9, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0_value:
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
    m_data: [32, 0],
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__1 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__4 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__7 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_StateT_instMonad___redArg___lam__9 as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_map as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__14_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_pure as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__15_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__16_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__13_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateT_bind as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__17_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__18_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21_value: crate::leanh::LeanArrayObject<1> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__20_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [42, 42, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24_value: crate::leanh::LeanArrayObject<1> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__23_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [36, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [36, 36, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27_value: crate::leanh::LeanArrayObject<2> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29_value: crate::leanh::LeanArrayObject<1> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__28_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [93, 40, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [33, 91, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [42, 32, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 32, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [46, 32, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1_value: crate::leanh::LeanArrayObject<1> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [62, 32, 0]};
static mut l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Doc_partMarkdown___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Doc_partMarkdown___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0(
    mut v_a_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1836_: u8 = 0;
    let mut v_fst_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1829_) == 0 {
                    v___x_1831_ = l_List_reverse___redArg(v_a_1830_);
                    return v___x_1831_;
                } else {
                    v_head_1832_ = crate::leanh::lean_ctor_get(v_a_1829_, 0);
                    v_tail_1833_ = crate::leanh::lean_ctor_get(v_a_1829_, 1);
                    v_isSharedCheck_1848_ = (!crate::leanh::lean_is_exclusive(v_a_1829_)) as u8;
                    if v_isSharedCheck_1848_ == 0 {
                        v___x_1835_ = v_a_1829_;
                        v_isShared_1836_ = v_isSharedCheck_1848_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1833_);
                        crate::leanh::lean_inc(v_head_1832_);
                        crate::leanh::lean_dec(v_a_1829_);
                        v___x_1835_ = crate::leanh::lean_box(0);
                        v_isShared_1836_ = v_isSharedCheck_1848_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1837_ = crate::leanh::lean_ctor_get(v_head_1832_, 0);
                crate::leanh::lean_inc(v_fst_1837_);
                v_snd_1838_ = crate::leanh::lean_ctor_get(v_head_1832_, 1);
                crate::leanh::lean_inc(v_snd_1838_);
                crate::leanh::lean_dec(v_head_1832_);
                v___x_1839_ =
                    l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0;
                v___x_1840_ = lean_string_append(v___x_1839_, v_fst_1837_);
                crate::leanh::lean_dec(v_fst_1837_);
                v___x_1841_ =
                    l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__1;
                v___x_1842_ = lean_string_append(v___x_1840_, v___x_1841_);
                v___x_1843_ = lean_string_append(v___x_1842_, v_snd_1838_);
                crate::leanh::lean_dec(v_snd_1838_);
                if v_isShared_1836_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1835_, 1, v_a_1830_);
                    crate::leanh::lean_ctor_set(v___x_1835_, 0, v___x_1843_);
                    v___x_1845_ = v___x_1835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1847_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1843_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_a_1830_);
                    v___x_1845_ = v_reuseFailAlloc_1847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1829_ = v_tail_1833_;
                v_a_1830_ = v___x_1845_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_MarkdownM_run_x27(
    mut v_act_1853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_main_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: u8 = 0;
    v___x_1854_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1855_ = l_Lean_Doc_MarkdownM_run_x27___closed__0;
    v___x_1856_ = crate::leanh::lean_apply_1(v_act_1853_, v___x_1855_);
    v_fst_1857_ = crate::leanh::lean_ctor_get(v___x_1856_, 0);
    crate::leanh::lean_inc(v_fst_1857_);
    v_snd_1858_ = crate::leanh::lean_ctor_get(v___x_1856_, 1);
    crate::leanh::lean_inc(v_snd_1858_);
    crate::leanh::lean_dec_ref(v___x_1856_);
    v___x_1859_ = l_Lean_Doc_MarkdownM_run_x27___closed__1;
    v___x_1860_ = lean_array_to_list(v_fst_1857_);
    v_main_1861_ = l_String_intercalate(v___x_1859_, v___x_1860_);
    v___x_1862_ = lean_array_get_size(v_snd_1858_);
    v___x_1863_ = lean_nat_dec_eq(v___x_1862_, v___x_1854_);
    if v___x_1863_ == 0 {
        let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_foots_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1864_ = lean_array_to_list(v_snd_1858_);
        v___x_1865_ = crate::leanh::lean_box(0);
        v_foots_1866_ =
            l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0(v___x_1864_, v___x_1865_);
        v___x_1867_ = l_Lean_Doc_MarkdownM_run_x27___closed__2;
        v___x_1868_ = lean_string_append(v_main_1861_, v___x_1867_);
        v___x_1869_ = l_String_intercalate(v___x_1867_, v_foots_1866_);
        v___x_1870_ = lean_string_append(v___x_1868_, v___x_1869_);
        crate::leanh::lean_dec_ref(v___x_1869_);
        return v___x_1870_;
    } else {
        crate::leanh::lean_dec(v_snd_1858_);
        return v_main_1861_;
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(
    mut v_s_1871_: *mut crate::leanh::LeanObject,
    mut v_pos_1872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: u8 = 0;
    let mut v___x_1879_: u32 = 0;
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: u32 = 0;
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1873_ = crate::leanh::lean_ctor_get(v_s_1871_, 0);
                v_startInclusive_1874_ = crate::leanh::lean_ctor_get(v_s_1871_, 1);
                v___x_1875_ = lean_nat_add(v_startInclusive_1874_, v_pos_1872_);
                v___x_1876_ = lean_nat_sub(v___x_1875_, v_startInclusive_1874_);
                v___x_1877_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1878_ = lean_nat_dec_eq(v___x_1876_, v___x_1877_);
                if v___x_1878_ == 0 {
                    v___x_1879_ = 32;
                    crate::leanh::lean_inc(v_startInclusive_1874_);
                    crate::leanh::lean_inc_ref(v_str_1873_);
                    v___x_1880_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1880_, 0, v_str_1873_);
                    crate::leanh::lean_ctor_set(v___x_1880_, 1, v_startInclusive_1874_);
                    crate::leanh::lean_ctor_set(v___x_1880_, 2, v___x_1875_);
                    v___x_1881_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1882_ = lean_nat_sub(v___x_1876_, v___x_1881_);
                    crate::leanh::lean_dec(v___x_1876_);
                    v___x_1883_ = l_String_Slice_posLE(v___x_1880_, v___x_1882_);
                    crate::leanh::lean_dec_ref_known(v___x_1880_, 3);
                    v___x_1884_ = lean_nat_add(v_startInclusive_1874_, v___x_1883_);
                    v___x_1885_ = lean_string_utf8_get_fast(v_str_1873_, v___x_1884_);
                    crate::leanh::lean_dec(v___x_1884_);
                    v___x_1886_ = lean_uint32_dec_eq(v___x_1885_, v___x_1879_);
                    if v___x_1886_ == 0 {
                        crate::leanh::lean_dec(v___x_1883_);
                        return v_pos_1872_;
                    } else {
                        v___x_1887_ = lean_nat_dec_lt(v___x_1883_, v_pos_1872_);
                        if v___x_1887_ == 0 {
                            crate::leanh::lean_dec(v___x_1883_);
                            return v_pos_1872_;
                        } else {
                            crate::leanh::lean_dec(v_pos_1872_);
                            v_pos_1872_ = v___x_1883_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1876_);
                    crate::leanh::lean_dec(v___x_1875_);
                    return v_pos_1872_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0___boxed(
    mut v_s_1889_: *mut crate::leanh::LeanObject,
    mut v_pos_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1891_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v_s_1889_, v_pos_1890_);
    crate::leanh::lean_dec_ref(v_s_1889_);
    return v_res_1891_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(
    mut v_s_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1894_ = lean_string_utf8_byte_size(v_s_1892_);
    crate::leanh::lean_inc_ref(v_s_1892_);
    v___x_1895_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1895_, 0, v_s_1892_);
    crate::leanh::lean_ctor_set(v___x_1895_, 1, v___x_1893_);
    crate::leanh::lean_ctor_set(v___x_1895_, 2, v___x_1894_);
    v___x_1896_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces_spec__0(v___x_1895_, v___x_1894_);
    crate::leanh::lean_dec_ref_known(v___x_1895_, 3);
    v___x_1897_ = lean_string_utf8_extract(v_s_1892_, v___x_1893_, v___x_1896_);
    crate::leanh::lean_dec(v___x_1896_);
    crate::leanh::lean_dec_ref(v_s_1892_);
    return v___x_1897_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(
    mut v_p_1898_: *mut crate::leanh::LeanObject,
    mut v_pTrim_1899_: *mut crate::leanh::LeanObject,
    mut v_sz_1900_: usize,
    mut v_i_1901_: usize,
    mut v_bs_1902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1903_: u8 = 0;
    let mut v_v_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: usize = 0;
    let mut v___x_1910_: usize = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1903_ = lean_usize_dec_lt(v_i_1901_, v_sz_1900_);
                if v___x_1903_ == 0 {
                    crate::leanh::lean_dec_ref(v_pTrim_1899_);
                    crate::leanh::lean_dec_ref(v_p_1898_);
                    return v_bs_1902_;
                } else {
                    v_v_1904_ = lean_array_uget(v_bs_1902_, v_i_1901_);
                    v___x_1905_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1906_ = lean_array_uset(v_bs_1902_, v_i_1901_, v___x_1905_);
                    v___x_1913_ = lean_string_utf8_byte_size(v_v_1904_);
                    v___x_1914_ = lean_nat_dec_eq(v___x_1913_, v___x_1905_);
                    if v___x_1914_ == 0 {
                        crate::leanh::lean_inc_ref(v_p_1898_);
                        v___x_1915_ = lean_string_append(v_p_1898_, v_v_1904_);
                        crate::leanh::lean_dec(v_v_1904_);
                        v___y_1908_ = v___x_1915_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_1904_);
                        crate::leanh::lean_inc_ref(v_pTrim_1899_);
                        v___y_1908_ = v_pTrim_1899_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1909_ = 1usize;
                v___x_1910_ = lean_usize_add(v_i_1901_, v___x_1909_);
                v___x_1911_ = lean_array_uset(v_bs_x27_1906_, v_i_1901_, v___y_1908_);
                v_i_1901_ = v___x_1910_;
                v_bs_1902_ = v___x_1911_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0___boxed(
    mut v_p_1916_: *mut crate::leanh::LeanObject,
    mut v_pTrim_1917_: *mut crate::leanh::LeanObject,
    mut v_sz_1918_: *mut crate::leanh::LeanObject,
    mut v_i_1919_: *mut crate::leanh::LeanObject,
    mut v_bs_1920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1921_: usize = 0;
    let mut v_i_boxed_1922_: usize = 0;
    let mut v_res_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1921_ = crate::leanh::lean_unbox_usize(v_sz_1918_);
    crate::leanh::lean_dec(v_sz_1918_);
    v_i_boxed_1922_ = crate::leanh::lean_unbox_usize(v_i_1919_);
    crate::leanh::lean_dec(v_i_1919_);
    v_res_1923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_1916_, v_pTrim_1917_, v_sz_boxed_1921_, v_i_boxed_1922_, v_bs_1920_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_Doc_prefixLines(
    mut v_p_1924_: *mut crate::leanh::LeanObject,
    mut v_lines_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pTrim_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1927_: usize = 0;
    let mut v___x_1928_: usize = 0;
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_p_1924_);
    v_pTrim_1926_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_p_1924_);
    v_sz_1927_ = lean_array_size(v_lines_1925_);
    v___x_1928_ = 0usize;
    v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_prefixLines_spec__0(v_p_1924_, v_pTrim_1926_, v_sz_1927_, v___x_1928_, v_lines_1925_);
    return v___x_1929_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(
    mut v_rest_1930_: *mut crate::leanh::LeanObject,
    mut v_restTrim_1931_: *mut crate::leanh::LeanObject,
    mut v_head_1932_: *mut crate::leanh::LeanObject,
    mut v_headTrim_1933_: *mut crate::leanh::LeanObject,
    mut v_as_1934_: *mut crate::leanh::LeanObject,
    mut v_i_1935_: *mut crate::leanh::LeanObject,
    mut v_j_1936_: *mut crate::leanh::LeanObject,
    mut v_bs_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1939_: u8 = 0;
    let mut v_one_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1938_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1939_ = lean_nat_dec_eq(v_i_1935_, v_zero_1938_);
                if v_isZero_1939_ == 1 {
                    crate::leanh::lean_dec(v_j_1936_);
                    crate::leanh::lean_dec(v_i_1935_);
                    crate::leanh::lean_dec_ref(v_headTrim_1933_);
                    crate::leanh::lean_dec_ref(v_head_1932_);
                    crate::leanh::lean_dec_ref(v_restTrim_1931_);
                    crate::leanh::lean_dec_ref(v_rest_1930_);
                    return v_bs_1937_;
                } else {
                    v_one_1940_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1941_ = lean_nat_sub(v_i_1935_, v_one_1940_);
                    crate::leanh::lean_dec(v_i_1935_);
                    v___x_1947_ = lean_array_fget_borrowed(v_as_1934_, v_j_1936_);
                    v___x_1954_ = lean_nat_dec_eq(v_j_1936_, v_zero_1938_);
                    if v___x_1954_ == 0 {
                        crate::leanh::lean_inc_ref(v_restTrim_1931_);
                        crate::leanh::lean_inc_ref(v_rest_1930_);
                        v_fst_1949_ = v_rest_1930_;
                        v_snd_1950_ = v_restTrim_1931_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_headTrim_1933_);
                        crate::leanh::lean_inc_ref(v_head_1932_);
                        v_fst_1949_ = v_head_1932_;
                        v_snd_1950_ = v_headTrim_1933_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1944_ = lean_nat_add(v_j_1936_, v_one_1940_);
                crate::leanh::lean_dec(v_j_1936_);
                v___x_1945_ = lean_array_push(v_bs_1937_, v___y_1943_);
                v_i_1935_ = v_n_1941_;
                v_j_1936_ = v___x_1944_;
                v_bs_1937_ = v___x_1945_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1951_ = lean_string_utf8_byte_size(v___x_1947_);
                v___x_1952_ = lean_nat_dec_eq(v___x_1951_, v_zero_1938_);
                if v___x_1952_ == 0 {
                    crate::leanh::lean_dec_ref(v_snd_1950_);
                    v___x_1953_ = lean_string_append(v_fst_1949_, v___x_1947_);
                    v___y_1943_ = v___x_1953_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_fst_1949_);
                    v___y_1943_ = v_snd_1950_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg___boxed(
    mut v_rest_1955_: *mut crate::leanh::LeanObject,
    mut v_restTrim_1956_: *mut crate::leanh::LeanObject,
    mut v_head_1957_: *mut crate::leanh::LeanObject,
    mut v_headTrim_1958_: *mut crate::leanh::LeanObject,
    mut v_as_1959_: *mut crate::leanh::LeanObject,
    mut v_i_1960_: *mut crate::leanh::LeanObject,
    mut v_j_1961_: *mut crate::leanh::LeanObject,
    mut v_bs_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(
        v_rest_1955_,
        v_restTrim_1956_,
        v_head_1957_,
        v_headTrim_1958_,
        v_as_1959_,
        v_i_1960_,
        v_j_1961_,
        v_bs_1962_,
    );
    crate::leanh::lean_dec_ref(v_as_1959_);
    return v_res_1963_;
}
pub unsafe fn l_Lean_Doc_prefixListLines(
    mut v_head_1964_: *mut crate::leanh::LeanObject,
    mut v_rest_1965_: *mut crate::leanh::LeanObject,
    mut v_lines_1966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_headTrim_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restTrim_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_head_1964_);
    v_headTrim_1967_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_head_1964_);
    crate::leanh::lean_inc_ref(v_rest_1965_);
    v_restTrim_1968_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimEndSpaces(v_rest_1965_);
    v___x_1969_ = lean_array_get_size(v_lines_1966_);
    v___x_1970_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1971_ = lean_mk_empty_array_with_capacity(v___x_1969_);
    v___x_1972_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(
        v_rest_1965_,
        v_restTrim_1968_,
        v_head_1964_,
        v_headTrim_1967_,
        v_lines_1966_,
        v___x_1969_,
        v___x_1970_,
        v___x_1971_,
    );
    return v___x_1972_;
}
pub unsafe fn l_Lean_Doc_prefixListLines___boxed(
    mut v_head_1973_: *mut crate::leanh::LeanObject,
    mut v_rest_1974_: *mut crate::leanh::LeanObject,
    mut v_lines_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_Lean_Doc_prefixListLines(v_head_1973_, v_rest_1974_, v_lines_1975_);
    crate::leanh::lean_dec_ref(v_lines_1975_);
    return v_res_1976_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0(
    mut v_rest_1977_: *mut crate::leanh::LeanObject,
    mut v_restTrim_1978_: *mut crate::leanh::LeanObject,
    mut v_head_1979_: *mut crate::leanh::LeanObject,
    mut v_headTrim_1980_: *mut crate::leanh::LeanObject,
    mut v_as_1981_: *mut crate::leanh::LeanObject,
    mut v_i_1982_: *mut crate::leanh::LeanObject,
    mut v_j_1983_: *mut crate::leanh::LeanObject,
    mut v_inv_1984_: *mut crate::leanh::LeanObject,
    mut v_bs_1985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1986_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___redArg(
        v_rest_1977_,
        v_restTrim_1978_,
        v_head_1979_,
        v_headTrim_1980_,
        v_as_1981_,
        v_i_1982_,
        v_j_1983_,
        v_bs_1985_,
    );
    return v___x_1986_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0___boxed(
    mut v_rest_1987_: *mut crate::leanh::LeanObject,
    mut v_restTrim_1988_: *mut crate::leanh::LeanObject,
    mut v_head_1989_: *mut crate::leanh::LeanObject,
    mut v_headTrim_1990_: *mut crate::leanh::LeanObject,
    mut v_as_1991_: *mut crate::leanh::LeanObject,
    mut v_i_1992_: *mut crate::leanh::LeanObject,
    mut v_j_1993_: *mut crate::leanh::LeanObject,
    mut v_inv_1994_: *mut crate::leanh::LeanObject,
    mut v_bs_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1996_ = l_Array_mapFinIdxM_map___at___00Lean_Doc_prefixListLines_spec__0(
        v_rest_1987_,
        v_restTrim_1988_,
        v_head_1989_,
        v_headTrim_1990_,
        v_as_1991_,
        v_i_1992_,
        v_j_1993_,
        v_inv_1994_,
        v_bs_1995_,
    );
    crate::leanh::lean_dec_ref(v_as_1991_);
    return v_res_1996_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(
    mut v_as_1998_: *mut crate::leanh::LeanObject,
    mut v_i_1999_: usize,
    mut v_stop_2000_: usize,
    mut v_b_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: usize = 0;
    let mut v___x_2005_: usize = 0;
    let mut v___x_2007_: u8 = 0;
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: u8 = 0;
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2007_ = lean_usize_dec_eq(v_i_1999_, v_stop_2000_);
                if v___x_2007_ == 0 {
                    v___x_2008_ = lean_array_uget_borrowed(v_as_1998_, v_i_1999_);
                    v___x_2009_ = lean_array_get_size(v___x_2008_);
                    v___x_2010_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2011_ = lean_nat_dec_eq(v___x_2009_, v___x_2010_);
                    if v___x_2011_ == 0 {
                        v___x_2012_ = lean_array_get_size(v_b_2001_);
                        v___x_2013_ = lean_nat_dec_eq(v___x_2012_, v___x_2010_);
                        if v___x_2013_ == 0 {
                            v___x_2014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0;
                            v___x_2015_ = lean_array_push(v_b_2001_, v___x_2014_);
                            v___x_2016_ = l_Array_append___redArg(v___x_2015_, v___x_2008_);
                            v___y_2003_ = v___x_2016_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2001_);
                            crate::leanh::lean_inc(v___x_2008_);
                            v___y_2003_ = v___x_2008_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_2003_ = v_b_2001_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2001_;
                }
            }
            1 => {
                v___x_2004_ = 1usize;
                v___x_2005_ = lean_usize_add(v_i_1999_, v___x_2004_);
                v_i_1999_ = v___x_2005_;
                v_b_2001_ = v___y_2003_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___boxed(
    mut v_as_2017_: *mut crate::leanh::LeanObject,
    mut v_i_2018_: *mut crate::leanh::LeanObject,
    mut v_stop_2019_: *mut crate::leanh::LeanObject,
    mut v_b_2020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2021_: usize = 0;
    let mut v_stop_boxed_2022_: usize = 0;
    let mut v_res_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2021_ = crate::leanh::lean_unbox_usize(v_i_2018_);
    crate::leanh::lean_dec(v_i_2018_);
    v_stop_boxed_2022_ = crate::leanh::lean_unbox_usize(v_stop_2019_);
    crate::leanh::lean_dec(v_stop_2019_);
    v_res_2023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_as_2017_, v_i_boxed_2021_, v_stop_boxed_2022_, v_b_2020_);
    crate::leanh::lean_dec_ref(v_as_2017_);
    return v_res_2023_;
}
pub unsafe fn l_Lean_Doc_joinBlocks(
    mut v_blocks_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: u8 = 0;
    v___x_2027_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2028_ = l_Lean_Doc_joinBlocks___closed__0;
    v___x_2029_ = lean_array_get_size(v_blocks_2026_);
    v___x_2030_ = lean_nat_dec_lt(v___x_2027_, v___x_2029_);
    if v___x_2030_ == 0 {
        return v___x_2028_;
    } else {
        let mut v___x_2031_: u8 = 0;
        v___x_2031_ = lean_nat_dec_le(v___x_2029_, v___x_2029_);
        if v___x_2031_ == 0 {
            if v___x_2030_ == 0 {
                return v___x_2028_;
            } else {
                let mut v___x_2032_: usize = 0;
                let mut v___x_2033_: usize = 0;
                let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2032_ = 0usize;
                v___x_2033_ = lean_usize_of_nat(v___x_2029_);
                v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_2026_, v___x_2032_, v___x_2033_, v___x_2028_);
                return v___x_2034_;
            }
        } else {
            let mut v___x_2035_: usize = 0;
            let mut v___x_2036_: usize = 0;
            let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2035_ = 0usize;
            v___x_2036_ = lean_usize_of_nat(v___x_2029_);
            v___x_2037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0(v_blocks_2026_, v___x_2035_, v___x_2036_, v___x_2028_);
            return v___x_2037_;
        }
    }
}
pub unsafe fn l_Lean_Doc_joinBlocks___boxed(
    mut v_blocks_2038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Lean_Doc_joinBlocks(v_blocks_2038_);
    crate::leanh::lean_dec_ref(v_blocks_2038_);
    return v_res_2039_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0;
    v___x_2042_ = lean_string_utf8_byte_size(v___x_2041_);
    return v___x_2042_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(
    mut v_l_2044_: *mut crate::leanh::LeanObject,
    mut v_r_2045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: u8 = 0;
    v___x_2046_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0;
    v___x_2047_ = lean_string_utf8_byte_size(v_l_2044_);
    v___x_2048_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once
        ),
        _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1,
    );
    v___x_2049_ = lean_nat_dec_le(v___x_2048_, v___x_2047_);
    if v___x_2049_ == 0 {
        let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2050_ = lean_string_append(v_l_2044_, v_r_2045_);
        return v___x_2050_;
    } else {
        let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: u8 = 0;
        v___x_2051_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2052_ = lean_nat_sub(v___x_2047_, v___x_2048_);
        v___x_2053_ = lean_string_memcmp(
            v_l_2044_,
            v___x_2046_,
            v___x_2052_,
            v___x_2051_,
            v___x_2048_,
        );
        crate::leanh::lean_dec(v___x_2052_);
        if v___x_2053_ == 0 {
            let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2054_ = lean_string_append(v_l_2044_, v_r_2045_);
            return v___x_2054_;
        } else {
            let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2056_: u8 = 0;
            v___x_2055_ = lean_string_utf8_byte_size(v_r_2045_);
            v___x_2056_ = lean_nat_dec_le(v___x_2048_, v___x_2055_);
            if v___x_2056_ == 0 {
                let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2057_ = lean_string_append(v_l_2044_, v_r_2045_);
                return v___x_2057_;
            } else {
                let mut v___x_2058_: u8 = 0;
                v___x_2058_ = lean_string_memcmp(
                    v_r_2045_,
                    v___x_2046_,
                    v___x_2051_,
                    v___x_2051_,
                    v___x_2048_,
                );
                if v___x_2058_ == 0 {
                    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2059_ = lean_string_append(v_l_2044_, v_r_2045_);
                    return v___x_2059_;
                } else {
                    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2060_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__2;
                    v___x_2061_ = lean_string_append(v_l_2044_, v___x_2060_);
                    v___x_2062_ = lean_string_append(v___x_2061_, v_r_2045_);
                    return v___x_2062_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___boxed(
    mut v_l_2063_: *mut crate::leanh::LeanObject,
    mut v_r_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2065_ =
        l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(v_l_2063_, v_r_2064_);
    crate::leanh::lean_dec_ref(v_r_2064_);
    return v_res_2065_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(
    mut v_as_2066_: *mut crate::leanh::LeanObject,
    mut v_i_2067_: usize,
    mut v_stop_2068_: usize,
    mut v_b_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: usize = 0;
    let mut v___x_2073_: usize = 0;
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastIdx_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_glued_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2075_ = lean_usize_dec_eq(v_i_2067_, v_stop_2068_);
                if v___x_2075_ == 0 {
                    v___x_2076_ = lean_array_uget_borrowed(v_as_2066_, v_i_2067_);
                    v___x_2077_ = lean_array_get_size(v___x_2076_);
                    v___x_2078_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2079_ = lean_nat_dec_eq(v___x_2077_, v___x_2078_);
                    if v___x_2079_ == 0 {
                        v___x_2080_ = lean_array_get_size(v_b_2069_);
                        v___x_2081_ = lean_nat_dec_eq(v___x_2080_, v___x_2078_);
                        if v___x_2081_ == 0 {
                            v___x_2082_ = crate::leanh::lean_unsigned_to_nat(1);
                            v_lastIdx_2083_ = lean_nat_sub(v___x_2080_, v___x_2082_);
                            v___x_2084_ = lean_array_fget_borrowed(v_b_2069_, v_lastIdx_2083_);
                            v___x_2085_ = lean_array_fget_borrowed(v___x_2076_, v___x_2078_);
                            crate::leanh::lean_inc(v___x_2084_);
                            v_glued_2086_ =
                                l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary(
                                    v___x_2084_,
                                    v___x_2085_,
                                );
                            v___x_2087_ =
                                lean_array_fset(v_b_2069_, v_lastIdx_2083_, v_glued_2086_);
                            crate::leanh::lean_dec(v_lastIdx_2083_);
                            v___x_2088_ =
                                l_Array_extract___redArg(v___x_2076_, v___x_2082_, v___x_2077_);
                            v___x_2089_ = l_Array_append___redArg(v___x_2087_, v___x_2088_);
                            crate::leanh::lean_dec_ref(v___x_2088_);
                            v___y_2071_ = v___x_2089_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2069_);
                            crate::leanh::lean_inc(v___x_2076_);
                            v___y_2071_ = v___x_2076_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_2071_ = v_b_2069_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2069_;
                }
            }
            1 => {
                v___x_2072_ = 1usize;
                v___x_2073_ = lean_usize_add(v_i_2067_, v___x_2072_);
                v_i_2067_ = v___x_2073_;
                v_b_2069_ = v___y_2071_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0___boxed(
    mut v_as_2090_: *mut crate::leanh::LeanObject,
    mut v_i_2091_: *mut crate::leanh::LeanObject,
    mut v_stop_2092_: *mut crate::leanh::LeanObject,
    mut v_b_2093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2094_: usize = 0;
    let mut v_stop_boxed_2095_: usize = 0;
    let mut v_res_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2094_ = crate::leanh::lean_unbox_usize(v_i_2091_);
    crate::leanh::lean_dec(v_i_2091_);
    v_stop_boxed_2095_ = crate::leanh::lean_unbox_usize(v_stop_2092_);
    crate::leanh::lean_dec(v_stop_2092_);
    v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_as_2090_, v_i_boxed_2094_, v_stop_boxed_2095_, v_b_2093_);
    crate::leanh::lean_dec_ref(v_as_2090_);
    return v_res_2096_;
}
pub unsafe fn l_Lean_Doc_joinInlines(
    mut v_parts_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: u8 = 0;
    v___x_2098_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2099_ = l_Lean_Doc_joinBlocks___closed__0;
    v___x_2100_ = lean_array_get_size(v_parts_2097_);
    v___x_2101_ = lean_nat_dec_lt(v___x_2098_, v___x_2100_);
    if v___x_2101_ == 0 {
        return v___x_2099_;
    } else {
        let mut v___x_2102_: u8 = 0;
        v___x_2102_ = lean_nat_dec_le(v___x_2100_, v___x_2100_);
        if v___x_2102_ == 0 {
            if v___x_2101_ == 0 {
                return v___x_2099_;
            } else {
                let mut v___x_2103_: usize = 0;
                let mut v___x_2104_: usize = 0;
                let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2103_ = 0usize;
                v___x_2104_ = lean_usize_of_nat(v___x_2100_);
                v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_2097_, v___x_2103_, v___x_2104_, v___x_2099_);
                return v___x_2105_;
            }
        } else {
            let mut v___x_2106_: usize = 0;
            let mut v___x_2107_: usize = 0;
            let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2106_ = 0usize;
            v___x_2107_ = lean_usize_of_nat(v___x_2100_);
            v___x_2108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinInlines_spec__0(v_parts_2097_, v___x_2106_, v___x_2107_, v___x_2099_);
            return v___x_2108_;
        }
    }
}
pub unsafe fn l_Lean_Doc_joinInlines___boxed(
    mut v_parts_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2110_ = l_Lean_Doc_joinInlines(v_parts_2109_);
    crate::leanh::lean_dec_ref(v_parts_2109_);
    return v_res_2110_;
}
pub unsafe fn l_Lean_Doc_instMarkdownInlineEmpty___lam__0(
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: u8,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
    mut v_a_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Lean_Doc_instMarkdownInlineEmpty___lam__0___boxed(
    mut v_a_2115_: *mut crate::leanh::LeanObject,
    mut v_a_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_13__boxed_2119_: u8 = 0;
    let mut v_res_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_13__boxed_2119_ = (crate::leanh::lean_unbox(v_a_2116_) as u8);
    v_res_2120_ = l_Lean_Doc_instMarkdownInlineEmpty___lam__0(
        v_a_2115_,
        v_a_13__boxed_2119_,
        v_a_2117_,
        v_a_2118_,
    );
    crate::leanh::lean_dec_ref(v_a_2118_);
    crate::leanh::lean_dec_ref(v_a_2117_);
    crate::leanh::lean_dec_ref(v_a_2115_);
    return v_res_2120_;
}
pub unsafe fn l_Lean_Doc_instMarkdownBlockEmpty___lam__0(
    mut v_a_2123_: *mut crate::leanh::LeanObject,
    mut v_a_2124_: *mut crate::leanh::LeanObject,
    mut v_a_2125_: u8,
    mut v_a_2126_: *mut crate::leanh::LeanObject,
    mut v_a_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Lean_Doc_instMarkdownBlockEmpty___lam__0___boxed(
    mut v_a_2128_: *mut crate::leanh::LeanObject,
    mut v_a_2129_: *mut crate::leanh::LeanObject,
    mut v_a_2130_: *mut crate::leanh::LeanObject,
    mut v_a_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_17__boxed_2133_: u8 = 0;
    let mut v_res_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_17__boxed_2133_ = (crate::leanh::lean_unbox(v_a_2130_) as u8);
    v_res_2134_ = l_Lean_Doc_instMarkdownBlockEmpty___lam__0(
        v_a_2128_,
        v_a_2129_,
        v_a_17__boxed_2133_,
        v_a_2131_,
        v_a_2132_,
    );
    crate::leanh::lean_dec_ref(v_a_2132_);
    crate::leanh::lean_dec_ref(v_a_2131_);
    crate::leanh::lean_dec_ref(v_a_2129_);
    crate::leanh::lean_dec_ref(v_a_2128_);
    return v_res_2134_;
}
pub unsafe fn l_Lean_Doc_instMarkdownBlockEmpty(
    mut v_i_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2137_ = l_Lean_Doc_instMarkdownBlockEmpty___closed__0;
    return v___f_2137_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(
    mut v_x_2138_: *mut crate::leanh::LeanObject,
    mut v_x_2139_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2138_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_2139_) == 0 {
            let mut v___x_2140_: u8 = 0;
            v___x_2140_ = 1;
            return v___x_2140_;
        } else {
            let mut v___x_2141_: u8 = 0;
            v___x_2141_ = 0;
            return v___x_2141_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_2139_) == 0 {
            let mut v___x_2142_: u8 = 0;
            v___x_2142_ = 0;
            return v___x_2142_;
        } else {
            let mut v_val_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2145_: u32 = 0;
            let mut v___x_2146_: u32 = 0;
            let mut v___x_2147_: u8 = 0;
            v_val_2143_ = crate::leanh::lean_ctor_get(v_x_2138_, 0);
            v_val_2144_ = crate::leanh::lean_ctor_get(v_x_2139_, 0);
            v___x_2145_ = crate::leanh::lean_unbox_uint32(v_val_2143_);
            v___x_2146_ = crate::leanh::lean_unbox_uint32(v_val_2144_);
            v___x_2147_ = lean_uint32_dec_eq(v___x_2145_, v___x_2146_);
            return v___x_2147_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1___boxed(
    mut v_x_2148_: *mut crate::leanh::LeanObject,
    mut v_x_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2150_: u8 = 0;
    let mut v_r_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2150_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_x_2148_, v_x_2149_);
    crate::leanh::lean_dec(v_x_2149_);
    crate::leanh::lean_dec(v_x_2148_);
    v_r_2151_ = crate::leanh::lean_box((v_res_2150_) as usize);
    return v_r_2151_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(
    mut v_s_2152_: *mut crate::leanh::LeanObject,
    mut v_c_2153_: u32,
    mut v_a_2154_: *mut crate::leanh::LeanObject,
    mut v_b_2155_: u8,
) -> u8 {
    let mut v_str_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u32 = 0;
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2156_ = crate::leanh::lean_ctor_get(v_s_2152_, 0);
                v_startInclusive_2157_ = crate::leanh::lean_ctor_get(v_s_2152_, 1);
                v_endExclusive_2158_ = crate::leanh::lean_ctor_get(v_s_2152_, 2);
                v___x_2159_ = lean_nat_sub(v_endExclusive_2158_, v_startInclusive_2157_);
                v___x_2160_ = lean_nat_dec_eq(v_a_2154_, v___x_2159_);
                crate::leanh::lean_dec(v___x_2159_);
                if v___x_2160_ == 0 {
                    v___x_2161_ = lean_nat_add(v_startInclusive_2157_, v_a_2154_);
                    crate::leanh::lean_dec(v_a_2154_);
                    v___x_2162_ = lean_string_utf8_get_fast(v_str_2156_, v___x_2161_);
                    v___x_2163_ = lean_uint32_dec_eq(v___x_2162_, v_c_2153_);
                    if v___x_2163_ == 0 {
                        v___x_2164_ = lean_string_utf8_next_fast(v_str_2156_, v___x_2161_);
                        crate::leanh::lean_dec(v___x_2161_);
                        v___x_2165_ = lean_nat_sub(v___x_2164_, v_startInclusive_2157_);
                        v_a_2154_ = v___x_2165_;
                        v_b_2155_ = v___x_2163_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2161_);
                        return v___x_2163_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2154_);
                    return v_b_2155_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg___boxed(
    mut v_s_2167_: *mut crate::leanh::LeanObject,
    mut v_c_2168_: *mut crate::leanh::LeanObject,
    mut v_a_2169_: *mut crate::leanh::LeanObject,
    mut v_b_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2171_: u32 = 0;
    let mut v_b_boxed_2172_: u8 = 0;
    let mut v_res_2173_: u8 = 0;
    let mut v_r_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2171_ = crate::leanh::lean_unbox_uint32(v_c_2168_);
    crate::leanh::lean_dec(v_c_2168_);
    v_b_boxed_2172_ = (crate::leanh::lean_unbox(v_b_2170_) as u8);
    v_res_2173_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_2167_, v_c_boxed_2171_, v_a_2169_, v_b_boxed_2172_);
    crate::leanh::lean_dec_ref(v_s_2167_);
    v_r_2174_ = crate::leanh::lean_box((v_res_2173_) as usize);
    return v_r_2174_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(
    mut v_c_2175_: u32,
    mut v_s_2176_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_searcher_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    let mut v___x_2179_: u8 = 0;
    v_searcher_2177_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2178_ = 0;
    v___x_2179_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_2176_, v_c_2175_, v_searcher_2177_, v___x_2178_);
    return v___x_2179_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0___boxed(
    mut v_c_2180_: *mut crate::leanh::LeanObject,
    mut v_s_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2182_: u32 = 0;
    let mut v_res_2183_: u8 = 0;
    let mut v_r_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2182_ = crate::leanh::lean_unbox_uint32(v_c_2180_);
    crate::leanh::lean_dec(v_c_2180_);
    v_res_2183_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_boxed_2182_, v_s_2181_);
    crate::leanh::lean_dec_ref(v_s_2181_);
    v_r_2184_ = crate::leanh::lean_box((v_res_2183_) as usize);
    return v_r_2184_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2186_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0;
    v___x_2187_ = lean_string_utf8_byte_size(v___x_2186_);
    return v___x_2187_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1_once
        ),
        _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__1,
    );
    v___x_2189_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2190_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__0;
    v___x_2191_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2191_, 0, v___x_2190_);
    crate::leanh::lean_ctor_set(v___x_2191_, 1, v___x_2189_);
    crate::leanh::lean_ctor_set(v___x_2191_, 2, v___x_2188_);
    return v___x_2191_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2192_: u32 = 0;
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = 91;
    v___x_2193_ = crate::leanh::lean_box_uint32(v___x_2192_);
    return v___x_2193_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2194_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1;
    v___x_2195_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2195_, 0, v___x_2194_);
    return v___x_2195_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(
    mut v_c_2196_: u32,
    mut v_next_x3f_2197_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2198_: u32 = 0;
    let mut v___x_2199_: u8 = 0;
    v___x_2198_ = 33;
    v___x_2199_ = lean_uint32_dec_eq(v_c_2196_, v___x_2198_);
    if v___x_2199_ == 0 {
        let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2201_: u8 = 0;
        v___x_2200_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2_once
            ),
            _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__2,
        );
        v___x_2201_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v_c_2196_, v___x_2200_);
        return v___x_2201_;
    } else {
        let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2203_: u8 = 0;
        v___x_2202_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3_once
            ),
            _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3,
        );
        v___x_2203_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_2197_, v___x_2202_);
        return v___x_2203_;
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___boxed(
    mut v_c_2204_: *mut crate::leanh::LeanObject,
    mut v_next_x3f_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2206_: u32 = 0;
    let mut v_res_2207_: u8 = 0;
    let mut v_r_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2206_ = crate::leanh::lean_unbox_uint32(v_c_2204_);
    crate::leanh::lean_dec(v_c_2204_);
    v_res_2207_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(
        v_c_boxed_2206_,
        v_next_x3f_2205_,
    );
    crate::leanh::lean_dec(v_next_x3f_2205_);
    v_r_2208_ = crate::leanh::lean_box((v_res_2207_) as usize);
    return v_r_2208_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(
    mut v_s_2209_: *mut crate::leanh::LeanObject,
    mut v_c_2210_: u32,
    mut v_inst_2211_: *mut crate::leanh::LeanObject,
    mut v_R_2212_: *mut crate::leanh::LeanObject,
    mut v_a_2213_: *mut crate::leanh::LeanObject,
    mut v_b_2214_: u8,
    mut v_c_2215_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2216_: u8 = 0;
    v___x_2216_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___redArg(v_s_2209_, v_c_2210_, v_a_2213_, v_b_2214_);
    return v___x_2216_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0___boxed(
    mut v_s_2217_: *mut crate::leanh::LeanObject,
    mut v_c_2218_: *mut crate::leanh::LeanObject,
    mut v_inst_2219_: *mut crate::leanh::LeanObject,
    mut v_R_2220_: *mut crate::leanh::LeanObject,
    mut v_a_2221_: *mut crate::leanh::LeanObject,
    mut v_b_2222_: *mut crate::leanh::LeanObject,
    mut v_c_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2224_: u32 = 0;
    let mut v_b_boxed_2225_: u8 = 0;
    let mut v_res_2226_: u8 = 0;
    let mut v_r_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2224_ = crate::leanh::lean_unbox_uint32(v_c_2218_);
    crate::leanh::lean_dec(v_c_2218_);
    v_b_boxed_2225_ = (crate::leanh::lean_unbox(v_b_2222_) as u8);
    v_res_2226_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0_spec__0(v_s_2217_, v_c_boxed_2224_, v_inst_2219_, v_R_2220_, v_a_2221_, v_b_boxed_2225_, v_c_2223_);
    crate::leanh::lean_dec_ref(v_s_2217_);
    v_r_2227_ = crate::leanh::lean_box((v_res_2226_) as usize);
    return v_r_2227_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2228_: u32 = 0;
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2228_ = 32;
    v___x_2229_ = crate::leanh::lean_box_uint32(v___x_2228_);
    return v___x_2229_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
    v___x_2231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2231_, 0, v___x_2230_);
    return v___x_2231_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(
    mut v_prev_x3f_2232_: *mut crate::leanh::LeanObject,
    mut v_c_2233_: u32,
    mut v_next_x3f_2234_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2236_: u8 = 0;
    let mut v___x_2237_: u32 = 0;
    let mut v___x_2238_: u8 = 0;
    let mut v___x_2239_: u32 = 0;
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: u32 = 0;
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2243_: u32 = 0;
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: u8 = 0;
    let mut v_val_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: u32 = 0;
    let mut v___x_2248_: u32 = 0;
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: u32 = 0;
    let mut v___x_2251_: u32 = 0;
    let mut v___x_2252_: u8 = 0;
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: u8 = 0;
    let mut v___x_2255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0), core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0_once), _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0);
                v___x_2254_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__1(v_next_x3f_2234_, v___x_2253_);
                if v___x_2254_ == 0 {
                    if crate::leanh::lean_obj_tag(v_next_x3f_2234_) == 0 {
                        v___x_2255_ = 1;
                        v___y_2236_ = v___x_2255_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2236_ = v___x_2254_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_2236_ = v___x_2254_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2237_ = 62;
                v___x_2238_ = lean_uint32_dec_eq(v_c_2233_, v___x_2237_);
                if v___x_2238_ == 0 {
                    v___x_2239_ = 45;
                    v___x_2240_ = lean_uint32_dec_eq(v_c_2233_, v___x_2239_);
                    if v___x_2240_ == 0 {
                        v___x_2241_ = 43;
                        v___x_2242_ = lean_uint32_dec_eq(v_c_2233_, v___x_2241_);
                        if v___x_2242_ == 0 {
                            v___x_2243_ = 46;
                            v___x_2244_ = lean_uint32_dec_eq(v_c_2233_, v___x_2243_);
                            if v___x_2244_ == 0 {
                                v___x_2245_ =
                                    l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(
                                        v_c_2233_,
                                        v_next_x3f_2234_,
                                    );
                                return v___x_2245_;
                            } else {
                                if crate::leanh::lean_obj_tag(v_prev_x3f_2232_) == 0 {
                                    return v___x_2242_;
                                } else {
                                    v_val_2246_ = crate::leanh::lean_ctor_get(v_prev_x3f_2232_, 0);
                                    v___x_2247_ = 48;
                                    v___x_2248_ = crate::leanh::lean_unbox_uint32(v_val_2246_);
                                    v___x_2249_ = lean_uint32_dec_le(v___x_2247_, v___x_2248_);
                                    if v___x_2249_ == 0 {
                                        if v___x_2249_ == 0 {
                                            return v___x_2249_;
                                        } else {
                                            return v___y_2236_;
                                        }
                                    } else {
                                        v___x_2250_ = 57;
                                        v___x_2251_ = crate::leanh::lean_unbox_uint32(v_val_2246_);
                                        v___x_2252_ = lean_uint32_dec_le(v___x_2251_, v___x_2250_);
                                        if v___x_2252_ == 0 {
                                            return v___x_2252_;
                                        } else {
                                            return v___y_2236_;
                                        }
                                    }
                                }
                            }
                        } else {
                            return v___y_2236_;
                        }
                    } else {
                        return v___y_2236_;
                    }
                } else {
                    return v___x_2238_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___boxed(
    mut v_prev_x3f_2256_: *mut crate::leanh::LeanObject,
    mut v_c_2257_: *mut crate::leanh::LeanObject,
    mut v_next_x3f_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2259_: u32 = 0;
    let mut v_res_2260_: u8 = 0;
    let mut v_r_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2259_ = crate::leanh::lean_unbox_uint32(v_c_2257_);
    crate::leanh::lean_dec(v_c_2257_);
    v_res_2260_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(
        v_prev_x3f_2256_,
        v_c_boxed_2259_,
        v_next_x3f_2258_,
    );
    crate::leanh::lean_dec(v_next_x3f_2258_);
    crate::leanh::lean_dec(v_prev_x3f_2256_);
    v_r_2261_ = crate::leanh::lean_box((v_res_2260_) as usize);
    return v_r_2261_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(
    mut v___x_2262_: u32,
    mut v___x_2263_: *mut crate::leanh::LeanObject,
    mut v_____r_2264_: *mut crate::leanh::LeanObject,
    mut v_s_x27_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2266_ = lean_string_push(v_s_x27_2265_, v___x_2262_);
    v___x_2267_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2267_, 0, v___x_2266_);
    crate::leanh::lean_ctor_set(v___x_2267_, 1, v___x_2263_);
    v___x_2268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2268_, 0, v___x_2267_);
    return v___x_2268_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0___boxed(
    mut v___x_2269_: *mut crate::leanh::LeanObject,
    mut v___x_2270_: *mut crate::leanh::LeanObject,
    mut v_____r_2271_: *mut crate::leanh::LeanObject,
    mut v_s_x27_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1739__boxed_2273_: u32 = 0;
    let mut v_res_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1739__boxed_2273_ = crate::leanh::lean_unbox_uint32(v___x_2269_);
    crate::leanh::lean_dec(v___x_2269_);
    v_res_2274_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_1739__boxed_2273_, v___x_2270_, v_____r_2271_, v_s_x27_2272_);
    return v_res_2274_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(
    mut v_s_2275_: *mut crate::leanh::LeanObject,
    mut v_a_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2286_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: u32 = 0;
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: u8 = 0;
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: u32 = 0;
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: u8 = 0;
    let mut v___x_2301_: u32 = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prev_x3f_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2282_ = crate::leanh::lean_ctor_get(v_a_2276_, 0);
                v_snd_2283_ = crate::leanh::lean_ctor_get(v_a_2276_, 1);
                v_isSharedCheck_2308_ = (!crate::leanh::lean_is_exclusive(v_a_2276_)) as u8;
                if v_isSharedCheck_2308_ == 0 {
                    v___x_2285_ = v_a_2276_;
                    v_isShared_2286_ = v_isSharedCheck_2308_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2283_);
                    crate::leanh::lean_inc(v_fst_2282_);
                    crate::leanh::lean_dec(v_a_2276_);
                    v___x_2285_ = crate::leanh::lean_box(0);
                    v_isShared_2286_ = v_isSharedCheck_2308_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2278_) == 0 {
                    v_a_2279_ = crate::leanh::lean_ctor_get(v___y_2278_, 0);
                    crate::leanh::lean_inc(v_a_2279_);
                    crate::leanh::lean_dec_ref_known(v___y_2278_, 1);
                    return v_a_2279_;
                } else {
                    v_a_2280_ = crate::leanh::lean_ctor_get(v___y_2278_, 0);
                    crate::leanh::lean_inc(v_a_2280_);
                    crate::leanh::lean_dec_ref_known(v___y_2278_, 1);
                    v_a_2276_ = v_a_2280_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_2287_ = lean_string_utf8_byte_size(v_s_2275_);
                v___x_2288_ = lean_nat_dec_eq(v_snd_2283_, v___x_2287_);
                if v___x_2288_ == 0 {
                    crate::leanh::lean_del_object(v___x_2285_);
                    v___x_2289_ = lean_string_utf8_get_fast(v_s_2275_, v_snd_2283_);
                    v___x_2290_ = lean_string_utf8_next_fast(v_s_2275_, v_snd_2283_);
                    crate::leanh::lean_dec(v_snd_2283_);
                    v___x_2300_ = lean_nat_dec_eq(v___x_2290_, v___x_2287_);
                    if v___x_2300_ == 0 {
                        v___x_2301_ = lean_string_utf8_get_fast(v_s_2275_, v___x_2290_);
                        v___x_2302_ = crate::leanh::lean_box_uint32(v___x_2301_);
                        v___x_2303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2303_, 0, v___x_2302_);
                        v___y_2292_ = v___x_2303_;
                        state = 3;
                        continue;
                    } else {
                        v_prev_x3f_2304_ = crate::leanh::lean_box(0);
                        v___y_2292_ = v_prev_x3f_2304_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2286_ == 0 {
                        v___x_2306_ = v___x_2285_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2307_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_fst_2282_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_snd_2283_);
                        v___x_2306_ = v_reuseFailAlloc_2307_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2293_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial(
                    v___x_2289_,
                    v___y_2292_,
                );
                crate::leanh::lean_dec(v___y_2292_);
                if v___x_2293_ == 0 {
                    v___x_2294_ = crate::leanh::lean_box(0);
                    v___x_2295_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_2289_, v___x_2290_, v___x_2294_, v_fst_2282_);
                    v___y_2278_ = v___x_2295_;
                    state = 1;
                    continue;
                } else {
                    v___x_2296_ = 92;
                    v___x_2297_ = lean_string_push(v_fst_2282_, v___x_2296_);
                    v___x_2298_ = crate::leanh::lean_box(0);
                    v___x_2299_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___lam__0(v___x_2289_, v___x_2290_, v___x_2298_, v___x_2297_);
                    v___y_2278_ = v___x_2299_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                return v___x_2306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg___boxed(
    mut v_s_2309_: *mut crate::leanh::LeanObject,
    mut v_a_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2311_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_2309_, v_a_2310_);
    crate::leanh::lean_dec_ref(v_s_2309_);
    return v_res_2311_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2313_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0;
    v___x_2314_ = lean_string_utf8_byte_size(v___x_2313_);
    return v___x_2314_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2315_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__1);
    v___x_2316_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2317_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__0;
    v___x_2318_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2318_, 0, v___x_2317_);
    crate::leanh::lean_ctor_set(v___x_2318_, 1, v___x_2316_);
    crate::leanh::lean_ctor_set(v___x_2318_, 2, v___x_2315_);
    return v___x_2318_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(
    mut v___x_2319_: u32,
    mut v___x_2320_: *mut crate::leanh::LeanObject,
    mut v_____r_2321_: *mut crate::leanh::LeanObject,
    mut v_s_x27_2322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2331_: u8 = 0;
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: u8 = 0;
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: u32 = 0;
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2339_: u32 = 0;
    let mut v___x_2340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2323_ = lean_string_push(v_s_x27_2322_, v___x_2319_);
                v___x_2324_ = crate::leanh::lean_box_uint32(v___x_2319_);
                v___x_2325_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2325_, 0, v___x_2324_);
                v___x_2337_ = 48;
                v___x_2338_ = lean_uint32_dec_le(v___x_2337_, v___x_2319_);
                if v___x_2338_ == 0 {
                    v___y_2331_ = v___x_2338_;
                    state = 2;
                    continue;
                } else {
                    v___x_2339_ = 57;
                    v___x_2340_ = lean_uint32_dec_le(v___x_2319_, v___x_2339_);
                    v___y_2331_ = v___x_2340_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2327_, 0, v___x_2320_);
                crate::leanh::lean_ctor_set(v___x_2327_, 1, v___x_2325_);
                v___x_2328_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2328_, 0, v___x_2323_);
                crate::leanh::lean_ctor_set(v___x_2328_, 1, v___x_2327_);
                v___x_2329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2329_, 0, v___x_2328_);
                return v___x_2329_;
            }
            2 => {
                if v___y_2331_ == 0 {
                    v___x_2332_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___closed__2);
                    v___x_2333_ = l_String_Slice_contains___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial_spec__0(v___x_2319_, v___x_2332_);
                    if v___x_2333_ == 0 {
                        v___x_2334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2334_, 0, v___x_2320_);
                        crate::leanh::lean_ctor_set(v___x_2334_, 1, v___x_2325_);
                        v___x_2335_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2323_);
                        crate::leanh::lean_ctor_set(v___x_2335_, 1, v___x_2334_);
                        v___x_2336_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2336_, 0, v___x_2335_);
                        return v___x_2336_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0___boxed(
    mut v___x_2341_: *mut crate::leanh::LeanObject,
    mut v___x_2342_: *mut crate::leanh::LeanObject,
    mut v_____r_2343_: *mut crate::leanh::LeanObject,
    mut v_s_x27_2344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1826__boxed_2345_: u32 = 0;
    let mut v_res_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1826__boxed_2345_ = crate::leanh::lean_unbox_uint32(v___x_2341_);
    crate::leanh::lean_dec(v___x_2341_);
    v_res_2346_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_1826__boxed_2345_, v___x_2342_, v_____r_2343_, v_s_x27_2344_);
    return v_res_2346_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(
    mut v_s_2347_: *mut crate::leanh::LeanObject,
    mut v_a_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v_fst_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2363_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    let mut v___x_2366_: u32 = 0;
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: u8 = 0;
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u32 = 0;
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: u32 = 0;
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prev_x3f_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2354_ = crate::leanh::lean_ctor_get(v_a_2348_, 1);
                v_fst_2355_ = crate::leanh::lean_ctor_get(v_a_2348_, 0);
                v_isSharedCheck_2389_ = (!crate::leanh::lean_is_exclusive(v_a_2348_)) as u8;
                if v_isSharedCheck_2389_ == 0 {
                    v___x_2357_ = v_a_2348_;
                    v_isShared_2358_ = v_isSharedCheck_2389_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2354_);
                    crate::leanh::lean_inc(v_fst_2355_);
                    crate::leanh::lean_dec(v_a_2348_);
                    v___x_2357_ = crate::leanh::lean_box(0);
                    v_isShared_2358_ = v_isSharedCheck_2389_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2350_) == 0 {
                    v_a_2351_ = crate::leanh::lean_ctor_get(v___y_2350_, 0);
                    crate::leanh::lean_inc(v_a_2351_);
                    crate::leanh::lean_dec_ref_known(v___y_2350_, 1);
                    return v_a_2351_;
                } else {
                    v_a_2352_ = crate::leanh::lean_ctor_get(v___y_2350_, 0);
                    crate::leanh::lean_inc(v_a_2352_);
                    crate::leanh::lean_dec_ref_known(v___y_2350_, 1);
                    v_a_2348_ = v_a_2352_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_fst_2359_ = crate::leanh::lean_ctor_get(v_snd_2354_, 0);
                v_snd_2360_ = crate::leanh::lean_ctor_get(v_snd_2354_, 1);
                v_isSharedCheck_2388_ = (!crate::leanh::lean_is_exclusive(v_snd_2354_)) as u8;
                if v_isSharedCheck_2388_ == 0 {
                    v___x_2362_ = v_snd_2354_;
                    v_isShared_2363_ = v_isSharedCheck_2388_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2360_);
                    crate::leanh::lean_inc(v_fst_2359_);
                    crate::leanh::lean_dec(v_snd_2354_);
                    v___x_2362_ = crate::leanh::lean_box(0);
                    v_isShared_2363_ = v_isSharedCheck_2388_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2364_ = lean_string_utf8_byte_size(v_s_2347_);
                v___x_2365_ = lean_nat_dec_eq(v_fst_2359_, v___x_2364_);
                if v___x_2365_ == 0 {
                    crate::leanh::lean_del_object(v___x_2362_);
                    crate::leanh::lean_del_object(v___x_2357_);
                    v___x_2366_ = lean_string_utf8_get_fast(v_s_2347_, v_fst_2359_);
                    v___x_2367_ = lean_string_utf8_next_fast(v_s_2347_, v_fst_2359_);
                    crate::leanh::lean_dec(v_fst_2359_);
                    v___x_2377_ = lean_nat_dec_eq(v___x_2367_, v___x_2364_);
                    if v___x_2377_ == 0 {
                        v___x_2378_ = lean_string_utf8_get_fast(v_s_2347_, v___x_2367_);
                        v___x_2379_ = crate::leanh::lean_box_uint32(v___x_2378_);
                        v___x_2380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2380_, 0, v___x_2379_);
                        v___y_2369_ = v___x_2380_;
                        state = 4;
                        continue;
                    } else {
                        v_prev_x3f_2381_ = crate::leanh::lean_box(0);
                        v___y_2369_ = v_prev_x3f_2381_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_2363_ == 0 {
                        v___x_2383_ = v___x_2362_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2387_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_fst_2359_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_snd_2360_);
                        v___x_2383_ = v_reuseFailAlloc_2387_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2370_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial(
                    v_snd_2360_,
                    v___x_2366_,
                    v___y_2369_,
                );
                crate::leanh::lean_dec(v___y_2369_);
                crate::leanh::lean_dec(v_snd_2360_);
                if v___x_2370_ == 0 {
                    v___x_2371_ = crate::leanh::lean_box(0);
                    v___x_2372_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_2366_, v___x_2367_, v___x_2371_, v_fst_2355_);
                    v___y_2350_ = v___x_2372_;
                    state = 1;
                    continue;
                } else {
                    v___x_2373_ = 92;
                    v___x_2374_ = lean_string_push(v_fst_2355_, v___x_2373_);
                    v___x_2375_ = crate::leanh::lean_box(0);
                    v___x_2376_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___lam__0(v___x_2366_, v___x_2367_, v___x_2375_, v___x_2374_);
                    v___y_2350_ = v___x_2376_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_2358_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2357_, 1, v___x_2383_);
                    v___x_2385_ = v___x_2357_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_fst_2355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 1, v___x_2383_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg___boxed(
    mut v_s_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2392_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_2390_, v_a_2391_);
    crate::leanh::lean_dec_ref(v_s_2390_);
    return v_res_2392_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(
    mut v_s_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2407_: u8 = 0;
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2413_: u8 = 0;
    let mut v_unused_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2400_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___closed__1;
                v___x_2401_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_2399_, v___x_2400_);
                v_snd_2402_ = crate::leanh::lean_ctor_get(v___x_2401_, 1);
                crate::leanh::lean_inc(v_snd_2402_);
                v_fst_2403_ = crate::leanh::lean_ctor_get(v___x_2401_, 0);
                crate::leanh::lean_inc(v_fst_2403_);
                crate::leanh::lean_dec_ref(v___x_2401_);
                v_fst_2404_ = crate::leanh::lean_ctor_get(v_snd_2402_, 0);
                v_isSharedCheck_2413_ = (!crate::leanh::lean_is_exclusive(v_snd_2402_)) as u8;
                if v_isSharedCheck_2413_ == 0 {
                    v_unused_2414_ = crate::leanh::lean_ctor_get(v_snd_2402_, 1);
                    crate::leanh::lean_dec(v_unused_2414_);
                    v___x_2406_ = v_snd_2402_;
                    v_isShared_2407_ = v_isSharedCheck_2413_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2404_);
                    crate::leanh::lean_dec(v_snd_2402_);
                    v___x_2406_ = crate::leanh::lean_box(0);
                    v_isShared_2407_ = v_isSharedCheck_2413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2406_, 1, v_fst_2404_);
                    crate::leanh::lean_ctor_set(v___x_2406_, 0, v_fst_2403_);
                    v___x_2409_ = v___x_2406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2412_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_fst_2403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_fst_2404_);
                    v___x_2409_ = v_reuseFailAlloc_2412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2410_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_2399_, v___x_2409_);
                v_fst_2411_ = crate::leanh::lean_ctor_get(v___x_2410_, 0);
                crate::leanh::lean_inc(v_fst_2411_);
                crate::leanh::lean_dec_ref(v___x_2410_);
                return v_fst_2411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_escape___boxed(
    mut v_s_2415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2416_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_s_2415_);
    crate::leanh::lean_dec_ref(v_s_2415_);
    return v_res_2416_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(
    mut v_s_2417_: *mut crate::leanh::LeanObject,
    mut v_inst_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___redArg(v_s_2417_, v_a_2419_);
    return v___x_2420_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0___boxed(
    mut v_s_2421_: *mut crate::leanh::LeanObject,
    mut v_inst_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__0(v_s_2421_, v_inst_2422_, v_a_2423_);
    crate::leanh::lean_dec_ref(v_s_2421_);
    return v_res_2424_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(
    mut v_s_2425_: *mut crate::leanh::LeanObject,
    mut v_inst_2426_: *mut crate::leanh::LeanObject,
    mut v_a_2427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2428_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___redArg(v_s_2425_, v_a_2427_);
    return v___x_2428_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1___boxed(
    mut v_s_2429_: *mut crate::leanh::LeanObject,
    mut v_inst_2430_: *mut crate::leanh::LeanObject,
    mut v_a_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2432_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_escape_spec__1(v_s_2429_, v_inst_2430_, v_a_2431_);
    crate::leanh::lean_dec_ref(v_s_2429_);
    return v_res_2432_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(
    mut v_str_2433_: *mut crate::leanh::LeanObject,
    mut v_a_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2439_: u8 = 0;
    let mut v_fst_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2444_: u8 = 0;
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: u8 = 0;
    let mut v___x_2447_: u32 = 0;
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: u32 = 0;
    let mut v___x_2450_: u8 = 0;
    let mut v_longest_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: u8 = 0;
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2477_: u8 = 0;
    let mut v_isSharedCheck_2478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2435_ = crate::leanh::lean_ctor_get(v_a_2434_, 1);
                v_fst_2436_ = crate::leanh::lean_ctor_get(v_a_2434_, 0);
                v_isSharedCheck_2478_ = (!crate::leanh::lean_is_exclusive(v_a_2434_)) as u8;
                if v_isSharedCheck_2478_ == 0 {
                    v___x_2438_ = v_a_2434_;
                    v_isShared_2439_ = v_isSharedCheck_2478_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2435_);
                    crate::leanh::lean_inc(v_fst_2436_);
                    crate::leanh::lean_dec(v_a_2434_);
                    v___x_2438_ = crate::leanh::lean_box(0);
                    v_isShared_2439_ = v_isSharedCheck_2478_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2440_ = crate::leanh::lean_ctor_get(v_snd_2435_, 0);
                v_snd_2441_ = crate::leanh::lean_ctor_get(v_snd_2435_, 1);
                v_isSharedCheck_2477_ = (!crate::leanh::lean_is_exclusive(v_snd_2435_)) as u8;
                if v_isSharedCheck_2477_ == 0 {
                    v___x_2443_ = v_snd_2435_;
                    v_isShared_2444_ = v_isSharedCheck_2477_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2441_);
                    crate::leanh::lean_inc(v_fst_2440_);
                    crate::leanh::lean_dec(v_snd_2435_);
                    v___x_2443_ = crate::leanh::lean_box(0);
                    v_isShared_2444_ = v_isSharedCheck_2477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2445_ = lean_string_utf8_byte_size(v_str_2433_);
                v___x_2446_ = lean_nat_dec_eq(v_snd_2441_, v___x_2445_);
                if v___x_2446_ == 0 {
                    v___x_2447_ = lean_string_utf8_get_fast(v_str_2433_, v_snd_2441_);
                    v___x_2448_ = lean_string_utf8_next_fast(v_str_2433_, v_snd_2441_);
                    crate::leanh::lean_dec(v_snd_2441_);
                    v___x_2449_ = 96;
                    v___x_2450_ = lean_uint32_dec_eq(v___x_2447_, v___x_2449_);
                    if v___x_2450_ == 0 {
                        v_longest_2451_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2461_ = lean_nat_dec_le(v_fst_2436_, v_fst_2440_);
                        if v___x_2461_ == 0 {
                            crate::leanh::lean_dec(v_fst_2440_);
                            v___y_2453_ = v_fst_2436_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fst_2436_);
                            v___y_2453_ = v_fst_2440_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2462_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2463_ = lean_nat_add(v_fst_2440_, v___x_2462_);
                        crate::leanh::lean_dec(v_fst_2440_);
                        if v_isShared_2444_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2443_, 1, v___x_2448_);
                            crate::leanh::lean_ctor_set(v___x_2443_, 0, v___x_2463_);
                            v___x_2465_ = v___x_2443_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2470_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2463_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 1, v___x_2448_);
                            v___x_2465_ = v_reuseFailAlloc_2470_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_2444_ == 0 {
                        v___x_2472_ = v___x_2443_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2476_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_fst_2440_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_snd_2441_);
                        v___x_2472_ = v_reuseFailAlloc_2476_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2443_, 1, v___x_2448_);
                    crate::leanh::lean_ctor_set(v___x_2443_, 0, v_longest_2451_);
                    v___x_2455_ = v___x_2443_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2460_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_longest_2451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2460_, 1, v___x_2448_);
                    v___x_2455_ = v_reuseFailAlloc_2460_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2439_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2438_, 1, v___x_2455_);
                    crate::leanh::lean_ctor_set(v___x_2438_, 0, v___y_2453_);
                    v___x_2457_ = v___x_2438_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2459_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___y_2453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2455_);
                    v___x_2457_ = v_reuseFailAlloc_2459_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_2434_ = v___x_2457_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2439_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2438_, 1, v___x_2465_);
                    v___x_2467_ = v___x_2438_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_fst_2436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2465_);
                    v___x_2467_ = v_reuseFailAlloc_2469_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_2434_ = v___x_2467_;
                state = 0;
                continue;
            }
            8 => {
                if v_isShared_2439_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2438_, 1, v___x_2472_);
                    v___x_2474_ = v___x_2438_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_fst_2436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2472_);
                    v___x_2474_ = v_reuseFailAlloc_2475_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(
    mut v_str_2479_: *mut crate::leanh::LeanObject,
    mut v_a_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_2479_, v_a_2480_);
    crate::leanh::lean_dec_ref(v_str_2479_);
    return v_res_2481_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(
    mut v_str_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: u8 = 0;
    v___x_2488_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___closed__1;
    v___x_2489_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_2487_, v___x_2488_);
    v_snd_2490_ = crate::leanh::lean_ctor_get(v___x_2489_, 1);
    crate::leanh::lean_inc(v_snd_2490_);
    v_fst_2491_ = crate::leanh::lean_ctor_get(v___x_2489_, 0);
    crate::leanh::lean_inc(v_fst_2491_);
    crate::leanh::lean_dec_ref(v___x_2489_);
    v_fst_2492_ = crate::leanh::lean_ctor_get(v_snd_2490_, 0);
    crate::leanh::lean_inc(v_fst_2492_);
    crate::leanh::lean_dec(v_snd_2490_);
    v___x_2493_ = lean_nat_dec_le(v_fst_2491_, v_fst_2492_);
    if v___x_2493_ == 0 {
        crate::leanh::lean_dec(v_fst_2492_);
        return v_fst_2491_;
    } else {
        crate::leanh::lean_dec(v_fst_2491_);
        return v_fst_2492_;
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun___boxed(
    mut v_str_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_2494_);
    crate::leanh::lean_dec_ref(v_str_2494_);
    return v_res_2495_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(
    mut v_str_2496_: *mut crate::leanh::LeanObject,
    mut v_inst_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2499_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___redArg(v_str_2496_, v_a_2498_);
    return v___x_2499_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0___boxed(
    mut v_str_2500_: *mut crate::leanh::LeanObject,
    mut v_inst_2501_: *mut crate::leanh::LeanObject,
    mut v_a_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2503_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun_spec__0(v_str_2500_, v_inst_2501_, v_a_2502_);
    crate::leanh::lean_dec_ref(v_str_2500_);
    return v_res_2503_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(
    mut v_x_2504_: *mut crate::leanh::LeanObject,
    mut v_x_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2507_: u8 = 0;
    let mut v___x_2508_: u32 = 0;
    let mut v_one_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2506_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2507_ = lean_nat_dec_eq(v_x_2504_, v_zero_2506_);
                if v_isZero_2507_ == 1 {
                    crate::leanh::lean_dec(v_x_2504_);
                    return v_x_2505_;
                } else {
                    v___x_2508_ = 96;
                    v_one_2509_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2510_ = lean_nat_sub(v_x_2504_, v_one_2509_);
                    crate::leanh::lean_dec(v_x_2504_);
                    v___x_2511_ = lean_string_push(v_x_2505_, v___x_2508_);
                    v_x_2504_ = v_n_2510_;
                    v_x_2505_ = v___x_2511_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(
    mut v_atLeast_2513_: *mut crate::leanh::LeanObject,
    mut v_str_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0;
                v___x_2521_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_longestBacktickRun(v_str_2514_);
                v___x_2522_ = lean_nat_dec_le(v_atLeast_2513_, v___x_2521_);
                if v___x_2522_ == 0 {
                    crate::leanh::lean_dec(v___x_2521_);
                    v___y_2517_ = v_atLeast_2513_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_atLeast_2513_);
                    v___y_2517_ = v___x_2521_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2518_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2519_ = lean_nat_add(v___y_2517_, v___x_2518_);
                crate::leanh::lean_dec(v___y_2517_);
                v___x_2520_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor_spec__0(v___x_2519_, v___x_2515_);
                return v___x_2520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor___boxed(
    mut v_atLeast_2523_: *mut crate::leanh::LeanObject,
    mut v_str_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2525_ =
        l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(v_atLeast_2523_, v_str_2524_);
    crate::leanh::lean_dec_ref(v_str_2524_);
    return v_res_2525_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(
    mut v_str_2527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_backticks_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: u8 = 0;
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2528_ = crate::leanh::lean_unsigned_to_nat(0);
                v_backticks_2529_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(
                    v___x_2528_,
                    v_str_2527_,
                );
                v___x_2545_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0;
                v___x_2546_ = lean_string_utf8_byte_size(v_str_2527_);
                v___x_2547_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1), core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once), _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
                v___x_2548_ = lean_nat_dec_le(v___x_2547_, v___x_2546_);
                if v___x_2548_ == 0 {
                    state = 3;
                    continue;
                } else {
                    v___x_2549_ = lean_string_memcmp(
                        v_str_2527_,
                        v___x_2545_,
                        v___x_2528_,
                        v___x_2528_,
                        v___x_2547_,
                    );
                    if v___x_2549_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_backticks_2529_);
                v___x_2532_ = lean_string_append(v_backticks_2529_, v___y_2531_);
                crate::leanh::lean_dec_ref(v___y_2531_);
                v___x_2533_ = lean_string_append(v___x_2532_, v_backticks_2529_);
                crate::leanh::lean_dec_ref(v_backticks_2529_);
                return v___x_2533_;
            }
            2 => {
                v___x_2535_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0;
                v___x_2536_ = lean_string_append(v___x_2535_, v_str_2527_);
                crate::leanh::lean_dec_ref(v_str_2527_);
                v___x_2537_ = lean_string_append(v___x_2536_, v___x_2535_);
                v___y_2531_ = v___x_2537_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2539_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__0;
                v___x_2540_ = lean_string_utf8_byte_size(v_str_2527_);
                v___x_2541_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1), core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1_once), _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_glueInlineBoundary___closed__1);
                v___x_2542_ = lean_nat_dec_le(v___x_2541_, v___x_2540_);
                if v___x_2542_ == 0 {
                    v___y_2531_ = v_str_2527_;
                    state = 1;
                    continue;
                } else {
                    v___x_2543_ = lean_nat_sub(v___x_2540_, v___x_2541_);
                    v___x_2544_ = lean_string_memcmp(
                        v_str_2527_,
                        v___x_2539_,
                        v___x_2543_,
                        v___x_2528_,
                        v___x_2541_,
                    );
                    crate::leanh::lean_dec(v___x_2543_);
                    if v___x_2544_ == 0 {
                        v___y_2531_ = v_str_2527_;
                        state = 1;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(
    mut v_s_2552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___closed__0;
    return v___x_2553_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0___boxed(
    mut v_s_2554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2555_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v_s_2554_);
    crate::leanh::lean_dec_ref(v_s_2554_);
    return v_res_2555_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(
    mut v_str_2556_: *mut crate::leanh::LeanObject,
    mut v___x_2557_: *mut crate::leanh::LeanObject,
    mut v___x_2558_: *mut crate::leanh::LeanObject,
    mut v_a_2559_: *mut crate::leanh::LeanObject,
    mut v_b_2560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v_startInclusive_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u8 = 0;
    let mut v___x_2577_: u32 = 0;
    let mut v___x_2578_: u32 = 0;
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2559_) == 0 {
                    v_currPos_2568_ = crate::leanh::lean_ctor_get(v_a_2559_, 0);
                    v_searcher_2569_ = crate::leanh::lean_ctor_get(v_a_2559_, 1);
                    v_isSharedCheck_2595_ = (!crate::leanh::lean_is_exclusive(v_a_2559_)) as u8;
                    if v_isSharedCheck_2595_ == 0 {
                        v___x_2571_ = v_a_2559_;
                        v_isShared_2572_ = v_isSharedCheck_2595_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_2569_);
                        crate::leanh::lean_inc(v_currPos_2568_);
                        crate::leanh::lean_dec(v_a_2559_);
                        v___x_2571_ = crate::leanh::lean_box(0);
                        v_isShared_2572_ = v_isSharedCheck_2595_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2558_);
                    return v_b_2560_;
                }
            }
            1 => {
                v___x_2565_ = lean_string_utf8_extract(
                    v_str_2556_,
                    v_startInclusive_2563_,
                    v_endExclusive_2564_,
                );
                crate::leanh::lean_dec(v_endExclusive_2564_);
                crate::leanh::lean_dec(v_startInclusive_2563_);
                v___x_2566_ = lean_array_push(v_b_2560_, v___x_2565_);
                v_a_2559_ = v_it_2562_;
                v_b_2560_ = v___x_2566_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_2573_ = crate::leanh::lean_ctor_get(v___x_2557_, 1);
                v_endExclusive_2574_ = crate::leanh::lean_ctor_get(v___x_2557_, 2);
                v___x_2575_ = lean_nat_sub(v_endExclusive_2574_, v_startInclusive_2573_);
                v___x_2576_ = lean_nat_dec_eq(v_searcher_2569_, v___x_2575_);
                crate::leanh::lean_dec(v___x_2575_);
                if v___x_2576_ == 0 {
                    v___x_2577_ = 10;
                    v___x_2578_ = lean_string_utf8_get_fast(v_str_2556_, v_searcher_2569_);
                    v___x_2579_ = lean_uint32_dec_eq(v___x_2578_, v___x_2577_);
                    if v___x_2579_ == 0 {
                        v___x_2580_ = lean_string_utf8_next_fast(v_str_2556_, v_searcher_2569_);
                        crate::leanh::lean_dec(v_searcher_2569_);
                        if v_isShared_2572_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2571_, 1, v___x_2580_);
                            v___x_2582_ = v___x_2571_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2584_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_currPos_2568_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2580_);
                            v___x_2582_ = v_reuseFailAlloc_2584_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2585_ = lean_string_utf8_next_fast(v_str_2556_, v_searcher_2569_);
                        v___x_2586_ = lean_nat_sub(v___x_2585_, v_searcher_2569_);
                        v___x_2587_ = lean_nat_add(v_searcher_2569_, v___x_2586_);
                        crate::leanh::lean_dec(v___x_2586_);
                        v_slice_2588_ = l_String_Slice_subslice_x21(
                            v___x_2557_,
                            v_currPos_2568_,
                            v_searcher_2569_,
                        );
                        crate::leanh::lean_inc(v___x_2587_);
                        if v_isShared_2572_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2571_, 1, v___x_2587_);
                            crate::leanh::lean_ctor_set(v___x_2571_, 0, v___x_2587_);
                            v_nextIt_2590_ = v___x_2571_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2593_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2587_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2593_, 1, v___x_2587_);
                            v_nextIt_2590_ = v_reuseFailAlloc_2593_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2571_);
                    crate::leanh::lean_dec(v_searcher_2569_);
                    v___x_2594_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_2558_);
                    v_it_2562_ = v___x_2594_;
                    v_startInclusive_2563_ = v_currPos_2568_;
                    v_endExclusive_2564_ = v___x_2558_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_2559_ = v___x_2582_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_2591_ = crate::leanh::lean_ctor_get(v_slice_2588_, 0);
                crate::leanh::lean_inc(v_startInclusive_2591_);
                v_endExclusive_2592_ = crate::leanh::lean_ctor_get(v_slice_2588_, 1);
                crate::leanh::lean_inc(v_endExclusive_2592_);
                crate::leanh::lean_dec_ref(v_slice_2588_);
                v_it_2562_ = v_nextIt_2590_;
                v_startInclusive_2563_ = v_startInclusive_2591_;
                v_endExclusive_2564_ = v_endExclusive_2592_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg___boxed(
    mut v_str_2596_: *mut crate::leanh::LeanObject,
    mut v___x_2597_: *mut crate::leanh::LeanObject,
    mut v___x_2598_: *mut crate::leanh::LeanObject,
    mut v_a_2599_: *mut crate::leanh::LeanObject,
    mut v_b_2600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2601_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_2596_, v___x_2597_, v___x_2598_, v_a_2599_, v_b_2600_);
    crate::leanh::lean_dec_ref(v___x_2597_);
    crate::leanh::lean_dec_ref(v_str_2596_);
    return v_res_2601_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(
    mut v_str_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2603_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2604_ = lean_string_utf8_byte_size(v_str_2602_);
    crate::leanh::lean_inc_ref(v_str_2602_);
    v___x_2605_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2605_, 0, v_str_2602_);
    crate::leanh::lean_ctor_set(v___x_2605_, 1, v___x_2603_);
    crate::leanh::lean_ctor_set(v___x_2605_, 2, v___x_2604_);
    v___x_2606_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__0(v___x_2605_);
    v___x_2607_ = l_Lean_Doc_joinBlocks___closed__0;
    v___x_2608_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_2602_, v___x_2605_, v___x_2604_, v___x_2606_, v___x_2607_);
    crate::leanh::lean_dec_ref_known(v___x_2605_, 3);
    crate::leanh::lean_dec_ref(v_str_2602_);
    return v___x_2608_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(
    mut v_str_2609_: *mut crate::leanh::LeanObject,
    mut v___x_2610_: *mut crate::leanh::LeanObject,
    mut v___x_2611_: *mut crate::leanh::LeanObject,
    mut v_inst_2612_: *mut crate::leanh::LeanObject,
    mut v_R_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
    mut v_b_2615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2616_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___redArg(v_str_2609_, v___x_2610_, v___x_2611_, v_a_2614_, v_b_2615_);
    return v___x_2616_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1___boxed(
    mut v_str_2617_: *mut crate::leanh::LeanObject,
    mut v___x_2618_: *mut crate::leanh::LeanObject,
    mut v___x_2619_: *mut crate::leanh::LeanObject,
    mut v_inst_2620_: *mut crate::leanh::LeanObject,
    mut v_R_2621_: *mut crate::leanh::LeanObject,
    mut v_a_2622_: *mut crate::leanh::LeanObject,
    mut v_b_2623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2624_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines_spec__1(v_str_2617_, v___x_2618_, v___x_2619_, v_inst_2620_, v_R_2621_, v_a_2622_, v_b_2623_);
    crate::leanh::lean_dec_ref(v___x_2618_);
    crate::leanh::lean_dec_ref(v_str_2617_);
    return v_res_2624_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(
    mut v_str_2625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fence_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2637_: u8 = 0;
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: u8 = 0;
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2626_ = crate::leanh::lean_unsigned_to_nat(2);
                v_fence_2627_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_fenceFor(
                    v___x_2626_,
                    v_str_2625_,
                );
                v_body_2635_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_splitNewlines(v_str_2625_);
                v___x_2639_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2640_ = lean_array_get_size(v_body_2635_);
                v___x_2641_ = lean_nat_dec_lt(v___x_2639_, v___x_2640_);
                if v___x_2641_ == 0 {
                    v___y_2637_ = v___x_2641_;
                    state = 2;
                    continue;
                } else {
                    v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0;
                    v___x_2643_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2644_ = lean_nat_sub(v___x_2640_, v___x_2643_);
                    v___x_2645_ = lean_array_get(v___x_2642_, v_body_2635_, v___x_2644_);
                    crate::leanh::lean_dec(v___x_2644_);
                    v___x_2646_ = lean_string_utf8_byte_size(v___x_2645_);
                    crate::leanh::lean_dec(v___x_2645_);
                    v___x_2647_ = lean_nat_dec_eq(v___x_2646_, v___x_2639_);
                    v___y_2637_ = v___x_2647_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2630_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2630_);
                v___x_2632_ = lean_array_push(v___x_2631_, v_fence_2627_);
                crate::leanh::lean_inc_ref(v___x_2632_);
                v___x_2633_ = l_Array_append___redArg(v___x_2632_, v___y_2629_);
                crate::leanh::lean_dec_ref(v___y_2629_);
                v___x_2634_ = l_Array_append___redArg(v___x_2633_, v___x_2632_);
                crate::leanh::lean_dec_ref(v___x_2632_);
                return v___x_2634_;
            }
            2 => {
                if v___y_2637_ == 0 {
                    v___y_2629_ = v_body_2635_;
                    state = 1;
                    continue;
                } else {
                    v___x_2638_ = lean_array_pop(v_body_2635_);
                    v___y_2629_ = v___x_2638_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(
    mut v_s_2648_: *mut crate::leanh::LeanObject,
    mut v_pos_2649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: u8 = 0;
    let mut v___y_2661_: u8 = 0;
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u8 = 0;
    let mut v___x_2665_: u32 = 0;
    let mut v___y_2667_: u8 = 0;
    let mut v___x_2668_: u32 = 0;
    let mut v___x_2669_: u8 = 0;
    let mut v___x_2670_: u32 = 0;
    let mut v___x_2671_: u8 = 0;
    let mut v___x_2672_: u32 = 0;
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: u32 = 0;
    let mut v___x_2675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2650_ = crate::leanh::lean_ctor_get(v_s_2648_, 0);
                v_startInclusive_2651_ = crate::leanh::lean_ctor_get(v_s_2648_, 1);
                v_endExclusive_2652_ = crate::leanh::lean_ctor_get(v_s_2648_, 2);
                v___x_2653_ = lean_nat_add(v_startInclusive_2651_, v_pos_2649_);
                v___x_2662_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2663_ = lean_nat_sub(v_endExclusive_2652_, v___x_2653_);
                v___x_2664_ = lean_nat_dec_eq(v___x_2662_, v___x_2663_);
                crate::leanh::lean_dec(v___x_2663_);
                if v___x_2664_ == 0 {
                    v___x_2665_ = lean_string_utf8_get_fast(v_str_2650_, v___x_2653_);
                    v___x_2672_ = 32;
                    v___x_2673_ = lean_uint32_dec_eq(v___x_2665_, v___x_2672_);
                    if v___x_2673_ == 0 {
                        v___x_2674_ = 9;
                        v___x_2675_ = lean_uint32_dec_eq(v___x_2665_, v___x_2674_);
                        v___y_2667_ = v___x_2675_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2667_ = v___x_2673_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2653_);
                    return v_pos_2649_;
                }
            }
            1 => {
                v___x_2655_ = lean_string_utf8_next_fast(v_str_2650_, v___x_2653_);
                v___x_2656_ = lean_nat_sub(v___x_2655_, v___x_2653_);
                crate::leanh::lean_dec(v___x_2653_);
                v___x_2657_ = lean_nat_add(v_pos_2649_, v___x_2656_);
                crate::leanh::lean_dec(v___x_2656_);
                v___x_2658_ = lean_nat_dec_lt(v_pos_2649_, v___x_2657_);
                if v___x_2658_ == 0 {
                    crate::leanh::lean_dec(v___x_2657_);
                    return v_pos_2649_;
                } else {
                    crate::leanh::lean_dec(v_pos_2649_);
                    v_pos_2649_ = v___x_2657_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_2661_ == 0 {
                    crate::leanh::lean_dec(v___x_2653_);
                    return v_pos_2649_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2667_ == 0 {
                    v___x_2668_ = 13;
                    v___x_2669_ = lean_uint32_dec_eq(v___x_2665_, v___x_2668_);
                    if v___x_2669_ == 0 {
                        v___x_2670_ = 10;
                        v___x_2671_ = lean_uint32_dec_eq(v___x_2665_, v___x_2670_);
                        v___y_2661_ = v___x_2671_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2661_ = v___x_2669_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0___boxed(
    mut v_s_2676_: *mut crate::leanh::LeanObject,
    mut v_pos_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v_s_2676_, v_pos_2677_);
    crate::leanh::lean_dec_ref(v_s_2676_);
    return v_res_2678_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2679_ = l_Lean_Doc_Inline_empty(crate::leanh::lean_box(0));
    return v___x_2679_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2680_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once
        ),
        _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0,
    );
    v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0;
    v___x_2682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2682_, 0, v___x_2681_);
    crate::leanh::lean_ctor_set(v___x_2682_, 1, v___x_2680_);
    return v___x_2682_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(
    mut v_a_2683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2689_: u8 = 0;
    let mut v_string_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2693_: u8 = 0;
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u8 = 0;
    let mut v_s1_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s2_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: u8 = 0;
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_unused_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2740_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: u8 = 0;
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2775_: u8 = 0;
    let mut v_unused_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2683_) == 0 {
                    v___x_2684_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1_once), _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__1);
                    return v___x_2684_;
                } else {
                    v_head_2685_ = crate::leanh::lean_ctor_get(v_a_2683_, 0);
                    crate::leanh::lean_inc(v_head_2685_);
                    match crate::leanh::lean_obj_tag(v_head_2685_) {
                        0 => {
                            v_tail_2686_ = crate::leanh::lean_ctor_get(v_a_2683_, 1);
                            v_isSharedCheck_2730_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2683_)) as u8;
                            if v_isSharedCheck_2730_ == 0 {
                                v_unused_2731_ = crate::leanh::lean_ctor_get(v_a_2683_, 0);
                                crate::leanh::lean_dec(v_unused_2731_);
                                v___x_2688_ = v_a_2683_;
                                v_isShared_2689_ = v_isSharedCheck_2730_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_tail_2686_);
                                crate::leanh::lean_dec(v_a_2683_);
                                v___x_2688_ = crate::leanh::lean_box(0);
                                v_isShared_2689_ = v_isSharedCheck_2730_;
                                state = 1;
                                continue;
                            }
                        }
                        9 => {
                            v_tail_2732_ = crate::leanh::lean_ctor_get(v_a_2683_, 1);
                            crate::leanh::lean_inc(v_tail_2732_);
                            crate::leanh::lean_dec_ref_known(v_a_2683_, 2);
                            v_content_2733_ = crate::leanh::lean_ctor_get(v_head_2685_, 0);
                            crate::leanh::lean_inc_ref(v_content_2733_);
                            crate::leanh::lean_dec_ref_known(v_head_2685_, 1);
                            v___x_2734_ = lean_array_to_list(v_content_2733_);
                            v___x_2735_ = l_List_appendTR___redArg(v___x_2734_, v_tail_2732_);
                            v_a_2683_ = v___x_2735_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v_tail_2737_ = crate::leanh::lean_ctor_get(v_a_2683_, 1);
                            v_isSharedCheck_2775_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2683_)) as u8;
                            if v_isSharedCheck_2775_ == 0 {
                                v_unused_2776_ = crate::leanh::lean_ctor_get(v_a_2683_, 0);
                                crate::leanh::lean_dec(v_unused_2776_);
                                v___x_2739_ = v_a_2683_;
                                v_isShared_2740_ = v_isSharedCheck_2775_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_tail_2737_);
                                crate::leanh::lean_dec(v_a_2683_);
                                v___x_2739_ = crate::leanh::lean_box(0);
                                v_isShared_2740_ = v_isSharedCheck_2775_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_string_2690_ = crate::leanh::lean_ctor_get(v_head_2685_, 0);
                v_isSharedCheck_2729_ = (!crate::leanh::lean_is_exclusive(v_head_2685_)) as u8;
                if v_isSharedCheck_2729_ == 0 {
                    v___x_2692_ = v_head_2685_;
                    v_isShared_2693_ = v_isSharedCheck_2729_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_string_2690_);
                    crate::leanh::lean_dec(v_head_2685_);
                    v___x_2692_ = crate::leanh::lean_box(0);
                    v_isShared_2693_ = v_isSharedCheck_2729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2694_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2695_ = lean_string_utf8_byte_size(v_string_2690_);
                crate::leanh::lean_inc_ref(v_string_2690_);
                v___x_2696_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2696_, 0, v_string_2690_);
                crate::leanh::lean_ctor_set(v___x_2696_, 1, v___x_2694_);
                crate::leanh::lean_ctor_set(v___x_2696_, 2, v___x_2695_);
                v___x_2697_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_2696_, v___x_2694_);
                crate::leanh::lean_dec_ref_known(v___x_2696_, 3);
                v___x_2698_ = lean_nat_dec_eq(v___x_2697_, v___x_2695_);
                if v___x_2698_ == 0 {
                    v_s1_2699_ = lean_string_utf8_extract(v_string_2690_, v___x_2694_, v___x_2697_);
                    v_s2_2700_ = lean_string_utf8_extract(v_string_2690_, v___x_2697_, v___x_2695_);
                    crate::leanh::lean_dec(v___x_2697_);
                    crate::leanh::lean_dec_ref(v_string_2690_);
                    if v_isShared_2693_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2692_, 0, v_s2_2700_);
                        v___x_2702_ = v___x_2692_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2717_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_s2_2700_);
                        v___x_2702_ = v_reuseFailAlloc_2717_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2697_);
                    crate::leanh::lean_del_object(v___x_2692_);
                    crate::leanh::lean_del_object(v___x_2688_);
                    v___x_2718_ =
                        l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(
                            v_tail_2686_,
                        );
                    v_fst_2719_ = crate::leanh::lean_ctor_get(v___x_2718_, 0);
                    v_snd_2720_ = crate::leanh::lean_ctor_get(v___x_2718_, 1);
                    v_isSharedCheck_2728_ = (!crate::leanh::lean_is_exclusive(v___x_2718_)) as u8;
                    if v_isSharedCheck_2728_ == 0 {
                        v___x_2722_ = v___x_2718_;
                        v_isShared_2723_ = v_isSharedCheck_2728_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2720_);
                        crate::leanh::lean_inc(v_fst_2719_);
                        crate::leanh::lean_dec(v___x_2718_);
                        v___x_2722_ = crate::leanh::lean_box(0);
                        v_isShared_2723_ = v_isSharedCheck_2728_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2703_ = lean_array_mk(v_tail_2686_);
                v___x_2704_ = lean_array_get_size(v___x_2703_);
                v___x_2705_ = lean_nat_dec_eq(v___x_2704_, v___x_2694_);
                if v___x_2705_ == 0 {
                    v___x_2706_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2707_ = lean_mk_empty_array_with_capacity(v___x_2706_);
                    v___x_2708_ = lean_array_push(v___x_2707_, v___x_2702_);
                    v___x_2709_ = l_Array_append___redArg(v___x_2708_, v___x_2703_);
                    crate::leanh::lean_dec_ref(v___x_2703_);
                    v___x_2710_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2710_, 0, v___x_2709_);
                    if v_isShared_2689_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2688_, 0);
                        crate::leanh::lean_ctor_set(v___x_2688_, 1, v___x_2710_);
                        crate::leanh::lean_ctor_set(v___x_2688_, 0, v_s1_2699_);
                        v___x_2712_ = v___x_2688_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_s1_2699_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2710_);
                        v___x_2712_ = v_reuseFailAlloc_2713_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2703_);
                    if v_isShared_2689_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2688_, 0);
                        crate::leanh::lean_ctor_set(v___x_2688_, 1, v___x_2702_);
                        crate::leanh::lean_ctor_set(v___x_2688_, 0, v_s1_2699_);
                        v___x_2715_ = v___x_2688_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_s1_2699_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2702_);
                        v___x_2715_ = v_reuseFailAlloc_2716_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2712_;
            }
            5 => {
                return v___x_2715_;
            }
            6 => {
                v___x_2724_ = lean_string_append(v_string_2690_, v_fst_2719_);
                crate::leanh::lean_dec(v_fst_2719_);
                if v_isShared_2723_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2722_, 0, v___x_2724_);
                    v___x_2726_ = v___x_2722_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_snd_2720_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2726_;
            }
            8 => {
                v___x_2741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0;
                v___x_2742_ = lean_array_mk(v_tail_2737_);
                if crate::leanh::lean_obj_tag(v_head_2685_) == 9 {
                    v_content_2743_ = crate::leanh::lean_ctor_get(v_head_2685_, 0);
                    v___x_2744_ = lean_array_get_size(v_content_2743_);
                    v___x_2745_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2746_ = lean_nat_dec_eq(v___x_2744_, v___x_2745_);
                    if v___x_2746_ == 0 {
                        v___x_2747_ = lean_array_get_size(v___x_2742_);
                        v___x_2748_ = lean_nat_dec_eq(v___x_2747_, v___x_2745_);
                        if v___x_2748_ == 0 {
                            crate::leanh::lean_inc_ref(v_content_2743_);
                            crate::leanh::lean_dec_ref_known(v_head_2685_, 1);
                            v___x_2749_ = l_Array_append___redArg(v_content_2743_, v___x_2742_);
                            crate::leanh::lean_dec_ref(v___x_2742_);
                            v___x_2750_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2750_, 0, v___x_2749_);
                            if v_isShared_2740_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2739_, 0);
                                crate::leanh::lean_ctor_set(v___x_2739_, 1, v___x_2750_);
                                crate::leanh::lean_ctor_set(v___x_2739_, 0, v___x_2741_);
                                v___x_2752_ = v___x_2739_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_2753_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2741_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2750_);
                                v___x_2752_ = v_reuseFailAlloc_2753_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2742_);
                            if v_isShared_2740_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2739_, 0);
                                crate::leanh::lean_ctor_set(v___x_2739_, 1, v_head_2685_);
                                crate::leanh::lean_ctor_set(v___x_2739_, 0, v___x_2741_);
                                v___x_2755_ = v___x_2739_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_2756_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2741_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2756_,
                                    1,
                                    v_head_2685_,
                                );
                                v___x_2755_ = v_reuseFailAlloc_2756_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_head_2685_, 1);
                        v___x_2757_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2757_, 0, v___x_2742_);
                        if v_isShared_2740_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2739_, 0);
                            crate::leanh::lean_ctor_set(v___x_2739_, 1, v___x_2757_);
                            crate::leanh::lean_ctor_set(v___x_2739_, 0, v___x_2741_);
                            v___x_2759_ = v___x_2739_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_2760_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2741_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2760_, 1, v___x_2757_);
                            v___x_2759_ = v_reuseFailAlloc_2760_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v___x_2761_ = lean_array_get_size(v___x_2742_);
                    v___x_2762_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2763_ = lean_nat_dec_eq(v___x_2761_, v___x_2762_);
                    if v___x_2763_ == 0 {
                        v___x_2764_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2765_ = lean_mk_empty_array_with_capacity(v___x_2764_);
                        v___x_2766_ = lean_array_push(v___x_2765_, v_head_2685_);
                        v___x_2767_ = l_Array_append___redArg(v___x_2766_, v___x_2742_);
                        crate::leanh::lean_dec_ref(v___x_2742_);
                        v___x_2768_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2768_, 0, v___x_2767_);
                        if v_isShared_2740_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2739_, 0);
                            crate::leanh::lean_ctor_set(v___x_2739_, 1, v___x_2768_);
                            crate::leanh::lean_ctor_set(v___x_2739_, 0, v___x_2741_);
                            v___x_2770_ = v___x_2739_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2771_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2741_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 1, v___x_2768_);
                            v___x_2770_ = v_reuseFailAlloc_2771_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2742_);
                        if v_isShared_2740_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2739_, 0);
                            crate::leanh::lean_ctor_set(v___x_2739_, 1, v_head_2685_);
                            crate::leanh::lean_ctor_set(v___x_2739_, 0, v___x_2741_);
                            v___x_2773_ = v___x_2739_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_2774_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2741_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_head_2685_);
                            v___x_2773_ = v_reuseFailAlloc_2774_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            9 => {
                return v___x_2752_;
            }
            10 => {
                return v___x_2755_;
            }
            11 => {
                return v___x_2759_;
            }
            12 => {
                return v___x_2770_;
            }
            13 => {
                return v___x_2773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go(
    mut v_i_2777_: *mut crate::leanh::LeanObject,
    mut v_a_2778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2779_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v_a_2778_);
    return v___x_2779_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(
    mut v_inline_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2781_ = crate::leanh::lean_box(0);
    v___x_2782_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2782_, 0, v_inline_2780_);
    crate::leanh::lean_ctor_set(v___x_2782_, 1, v___x_2781_);
    v___x_2783_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg(v___x_2782_);
    return v___x_2783_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft(
    mut v_i_2784_: *mut crate::leanh::LeanObject,
    mut v_inline_2785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2786_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(v_inline_2785_);
    return v___x_2786_;
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(
    mut v_s_2787_: *mut crate::leanh::LeanObject,
    mut v_pos_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___y_2803_: u8 = 0;
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: u32 = 0;
    let mut v___y_2807_: u8 = 0;
    let mut v___x_2808_: u32 = 0;
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2810_: u32 = 0;
    let mut v___x_2811_: u8 = 0;
    let mut v___x_2812_: u32 = 0;
    let mut v___x_2813_: u8 = 0;
    let mut v___x_2814_: u32 = 0;
    let mut v___x_2815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2789_ = crate::leanh::lean_ctor_get(v_s_2787_, 0);
                v_startInclusive_2790_ = crate::leanh::lean_ctor_get(v_s_2787_, 1);
                v___x_2791_ = lean_nat_add(v_startInclusive_2790_, v_pos_2788_);
                v___x_2792_ = lean_nat_sub(v___x_2791_, v_startInclusive_2790_);
                v___x_2793_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2794_ = lean_nat_dec_eq(v___x_2792_, v___x_2793_);
                if v___x_2794_ == 0 {
                    crate::leanh::lean_inc(v_startInclusive_2790_);
                    crate::leanh::lean_inc_ref(v_str_2789_);
                    v___x_2795_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2795_, 0, v_str_2789_);
                    crate::leanh::lean_ctor_set(v___x_2795_, 1, v_startInclusive_2790_);
                    crate::leanh::lean_ctor_set(v___x_2795_, 2, v___x_2791_);
                    v___x_2796_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2797_ = lean_nat_sub(v___x_2792_, v___x_2796_);
                    crate::leanh::lean_dec(v___x_2792_);
                    v___x_2798_ = l_String_Slice_posLE(v___x_2795_, v___x_2797_);
                    crate::leanh::lean_dec_ref_known(v___x_2795_, 3);
                    v___x_2804_ = lean_nat_add(v_startInclusive_2790_, v___x_2798_);
                    v___x_2805_ = lean_string_utf8_get_fast(v_str_2789_, v___x_2804_);
                    crate::leanh::lean_dec(v___x_2804_);
                    v___x_2812_ = 32;
                    v___x_2813_ = lean_uint32_dec_eq(v___x_2805_, v___x_2812_);
                    if v___x_2813_ == 0 {
                        v___x_2814_ = 9;
                        v___x_2815_ = lean_uint32_dec_eq(v___x_2805_, v___x_2814_);
                        v___y_2807_ = v___x_2815_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2807_ = v___x_2813_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2792_);
                    crate::leanh::lean_dec(v___x_2791_);
                    return v_pos_2788_;
                }
            }
            1 => {
                v___x_2800_ = lean_nat_dec_lt(v___x_2798_, v_pos_2788_);
                if v___x_2800_ == 0 {
                    crate::leanh::lean_dec(v___x_2798_);
                    return v_pos_2788_;
                } else {
                    crate::leanh::lean_dec(v_pos_2788_);
                    v_pos_2788_ = v___x_2798_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_2803_ == 0 {
                    crate::leanh::lean_dec(v___x_2798_);
                    return v_pos_2788_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2807_ == 0 {
                    v___x_2808_ = 13;
                    v___x_2809_ = lean_uint32_dec_eq(v___x_2805_, v___x_2808_);
                    if v___x_2809_ == 0 {
                        v___x_2810_ = 10;
                        v___x_2811_ = lean_uint32_dec_eq(v___x_2805_, v___x_2810_);
                        v___y_2803_ = v___x_2811_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2803_ = v___x_2809_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0___boxed(
    mut v_s_2816_: *mut crate::leanh::LeanObject,
    mut v_pos_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2818_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v_s_2816_, v_pos_2817_);
    crate::leanh::lean_dec_ref(v_s_2816_);
    return v_res_2818_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0;
    v___x_2820_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0_once
        ),
        _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go___redArg___closed__0,
    );
    v___x_2821_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2820_);
    crate::leanh::lean_ctor_set(v___x_2821_, 1, v___x_2819_);
    return v___x_2821_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(
    mut v_xs_2822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_string_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: u8 = 0;
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2858_: u8 = 0;
    let mut v_isSharedCheck_2859_: u8 = 0;
    let mut v_content_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2823_ = lean_array_get_size(v_xs_2822_);
                v___x_2824_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2825_ = lean_nat_dec_eq(v___x_2823_, v___x_2824_);
                if v___x_2825_ == 0 {
                    v___x_2826_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2827_ = lean_nat_sub(v___x_2823_, v___x_2826_);
                    v___x_2828_ = lean_array_fget(v_xs_2822_, v___x_2827_);
                    crate::leanh::lean_dec(v___x_2827_);
                    match crate::leanh::lean_obj_tag(v___x_2828_) {
                        0 => {
                            v_string_2829_ = crate::leanh::lean_ctor_get(v___x_2828_, 0);
                            v_isSharedCheck_2859_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2828_)) as u8;
                            if v_isSharedCheck_2859_ == 0 {
                                v___x_2831_ = v___x_2828_;
                                v_isShared_2832_ = v_isSharedCheck_2859_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_string_2829_);
                                crate::leanh::lean_dec(v___x_2828_);
                                v___x_2831_ = crate::leanh::lean_box(0);
                                v_isShared_2832_ = v_isSharedCheck_2859_;
                                state = 1;
                                continue;
                            }
                        }
                        9 => {
                            v_content_2860_ = crate::leanh::lean_ctor_get(v___x_2828_, 0);
                            crate::leanh::lean_inc_ref(v_content_2860_);
                            crate::leanh::lean_dec_ref_known(v___x_2828_, 1);
                            v___x_2861_ = lean_array_pop(v_xs_2822_);
                            v___x_2862_ = l_Array_append___redArg(v___x_2861_, v_content_2860_);
                            crate::leanh::lean_dec_ref(v_content_2860_);
                            v_xs_2822_ = v___x_2862_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v___x_2828_);
                            v___x_2864_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2864_, 0, v_xs_2822_);
                            v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0;
                            v___x_2866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2866_, 0, v___x_2864_);
                            crate::leanh::lean_ctor_set(v___x_2866_, 1, v___x_2865_);
                            return v___x_2866_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_xs_2822_);
                    v___x_2867_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0_once), _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg___closed__0);
                    return v___x_2867_;
                }
            }
            1 => {
                v___x_2833_ = lean_string_utf8_byte_size(v_string_2829_);
                crate::leanh::lean_inc_ref(v_string_2829_);
                v___x_2834_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2834_, 0, v_string_2829_);
                crate::leanh::lean_ctor_set(v___x_2834_, 1, v___x_2824_);
                crate::leanh::lean_ctor_set(v___x_2834_, 2, v___x_2833_);
                v___x_2835_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft_go_spec__0(v___x_2834_, v___x_2824_);
                v___x_2836_ = lean_nat_dec_eq(v___x_2835_, v___x_2833_);
                crate::leanh::lean_dec(v___x_2835_);
                if v___x_2836_ == 0 {
                    v___x_2837_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go_spec__0(v___x_2834_, v___x_2833_);
                    crate::leanh::lean_dec_ref_known(v___x_2834_, 3);
                    v___x_2838_ = lean_array_pop(v_xs_2822_);
                    v___x_2839_ =
                        lean_string_utf8_extract(v_string_2829_, v___x_2824_, v___x_2837_);
                    if v_isShared_2832_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2831_, 0, v___x_2839_);
                        v___x_2841_ = v___x_2831_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2839_);
                        v___x_2841_ = v_reuseFailAlloc_2846_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2834_, 3);
                    crate::leanh::lean_del_object(v___x_2831_);
                    v___x_2847_ = lean_array_pop(v_xs_2822_);
                    v___x_2848_ =
                        l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(
                            v___x_2847_,
                        );
                    v_fst_2849_ = crate::leanh::lean_ctor_get(v___x_2848_, 0);
                    v_snd_2850_ = crate::leanh::lean_ctor_get(v___x_2848_, 1);
                    v_isSharedCheck_2858_ = (!crate::leanh::lean_is_exclusive(v___x_2848_)) as u8;
                    if v_isSharedCheck_2858_ == 0 {
                        v___x_2852_ = v___x_2848_;
                        v_isShared_2853_ = v_isSharedCheck_2858_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2850_);
                        crate::leanh::lean_inc(v_fst_2849_);
                        crate::leanh::lean_dec(v___x_2848_);
                        v___x_2852_ = crate::leanh::lean_box(0);
                        v_isShared_2853_ = v_isSharedCheck_2858_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2842_ = lean_array_push(v___x_2838_, v___x_2841_);
                v___x_2843_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2843_, 0, v___x_2842_);
                v___x_2844_ = lean_string_utf8_extract(v_string_2829_, v___x_2837_, v___x_2833_);
                crate::leanh::lean_dec(v___x_2837_);
                crate::leanh::lean_dec_ref(v_string_2829_);
                v___x_2845_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2845_, 0, v___x_2843_);
                crate::leanh::lean_ctor_set(v___x_2845_, 1, v___x_2844_);
                return v___x_2845_;
            }
            3 => {
                v___x_2854_ = lean_string_append(v_snd_2850_, v_string_2829_);
                crate::leanh::lean_dec_ref(v_string_2829_);
                if v_isShared_2853_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2852_, 1, v___x_2854_);
                    v___x_2856_ = v___x_2852_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_fst_2849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2857_, 1, v___x_2854_);
                    v___x_2856_ = v_reuseFailAlloc_2857_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go(
    mut v_i_2868_: *mut crate::leanh::LeanObject,
    mut v_xs_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2870_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v_xs_2869_);
    return v___x_2870_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(
    mut v_inline_2871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2873_ = lean_mk_empty_array_with_capacity(v___x_2872_);
    v___x_2874_ = lean_array_push(v___x_2873_, v_inline_2871_);
    v___x_2875_ =
        l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight_go___redArg(v___x_2874_);
    return v___x_2875_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight(
    mut v_i_2876_: *mut crate::leanh::LeanObject,
    mut v_inline_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2878_ =
        l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_inline_2877_);
    return v___x_2878_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(
    mut v_inline_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2885_: u8 = 0;
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2890_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2880_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trimLeft___redArg(
                    v_inline_2879_,
                );
                v_fst_2881_ = crate::leanh::lean_ctor_get(v___x_2880_, 0);
                v_snd_2882_ = crate::leanh::lean_ctor_get(v___x_2880_, 1);
                v_isSharedCheck_2890_ = (!crate::leanh::lean_is_exclusive(v___x_2880_)) as u8;
                if v_isSharedCheck_2890_ == 0 {
                    v___x_2884_ = v___x_2880_;
                    v_isShared_2885_ = v_isSharedCheck_2890_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2882_);
                    crate::leanh::lean_inc(v_fst_2881_);
                    crate::leanh::lean_dec(v___x_2880_);
                    v___x_2884_ = crate::leanh::lean_box(0);
                    v_isShared_2885_ = v_isSharedCheck_2890_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2886_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_trimRight___redArg(v_snd_2882_);
                if v_isShared_2885_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2884_, 1, v___x_2886_);
                    v___x_2888_ = v___x_2884_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2889_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_fst_2881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 1, v___x_2886_);
                    v___x_2888_ = v_reuseFailAlloc_2889_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(
    mut v_i_2891_: *mut crate::leanh::LeanObject,
    mut v_inline_2892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2893_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v_inline_2892_);
    return v___x_2893_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2965_ =
        l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__29;
    v___x_2966_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_2967_ = lean_mk_empty_array_with_capacity(v___x_2966_);
    v___x_2968_ = lean_array_push(v___x_2967_, v___x_2965_);
    return v___x_2968_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(
    mut v_inst_2971_: *mut crate::leanh::LeanObject,
    mut v_x_2972_: *mut crate::leanh::LeanObject,
    mut v_x_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pieces_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pieces_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_string_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2995_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pieces_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inEmph_3013_: u8 = 0;
    let mut v_inBold_3014_: u8 = 0;
    let mut v_inLink_3015_: u8 = 0;
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pieces_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pieces_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: u8 = 0;
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3044_: u8 = 0;
    let mut v_reuseFailAlloc_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3046_: u8 = 0;
    let mut v_content_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pieces_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inEmph_3068_: u8 = 0;
    let mut v_inBold_3069_: u8 = 0;
    let mut v_inLink_3070_: u8 = 0;
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v___x_3074_: u8 = 0;
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pieces_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pieces_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut v_reuseFailAlloc_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v_string_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mode_3108_: u8 = 0;
    let mut v_string_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_string_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inLink_3127_: u8 = 0;
    let mut v_content_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inEmph_3130_: u8 = 0;
    let mut v_inBold_3131_: u8 = 0;
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3144_: u8 = 0;
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3159_: u8 = 0;
    let mut v_reuseFailAlloc_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut v_content_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3164_: usize = 0;
    let mut v___x_3165_: usize = 0;
    let mut v___x_5248__overap_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut v_name_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3181_: usize = 0;
    let mut v___x_3182_: usize = 0;
    let mut v___x_5251__overap_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3206_: u8 = 0;
    let mut v_alt_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_url_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3223_: usize = 0;
    let mut v___x_3224_: usize = 0;
    let mut v___x_5254__overap_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3231_: u8 = 0;
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_container_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2985_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19;
                match crate::leanh::lean_obj_tag(v_x_2973_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_x_2972_);
                        crate::leanh::lean_dec_ref(v_inst_2971_);
                        v_string_2986_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                        crate::leanh::lean_inc_ref(v_string_2986_);
                        crate::leanh::lean_dec_ref_known(v_x_2973_, 1);
                        v___x_2987_ =
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_2986_);
                        crate::leanh::lean_dec_ref(v_string_2986_);
                        v___x_2988_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2989_ = lean_mk_empty_array_with_capacity(v___x_2988_);
                        v___x_2990_ = lean_array_push(v___x_2989_, v___x_2987_);
                        v___x_2991_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2991_, 0, v___x_2990_);
                        crate::leanh::lean_ctor_set(v___x_2991_, 1, v_a_2974_);
                        return v___x_2991_;
                    }
                    1 => {
                        v_content_2992_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                        v_isSharedCheck_3046_ = (!crate::leanh::lean_is_exclusive(v_x_2973_)) as u8;
                        if v_isSharedCheck_3046_ == 0 {
                            v___x_2994_ = v_x_2973_;
                            v_isShared_2995_ = v_isSharedCheck_3046_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_content_2992_);
                            crate::leanh::lean_dec(v_x_2973_);
                            v___x_2994_ = crate::leanh::lean_box(0);
                            v_isShared_2995_ = v_isSharedCheck_3046_;
                            state = 3;
                            continue;
                        }
                    }
                    2 => {
                        v_content_3047_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                        v_isSharedCheck_3101_ = (!crate::leanh::lean_is_exclusive(v_x_2973_)) as u8;
                        if v_isSharedCheck_3101_ == 0 {
                            v___x_3049_ = v_x_2973_;
                            v_isShared_3050_ = v_isSharedCheck_3101_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_content_3047_);
                            crate::leanh::lean_dec(v_x_2973_);
                            v___x_3049_ = crate::leanh::lean_box(0);
                            v_isShared_3050_ = v_isSharedCheck_3101_;
                            state = 10;
                            continue;
                        }
                    }
                    3 => {
                        crate::leanh::lean_dec_ref(v_x_2972_);
                        crate::leanh::lean_dec_ref(v_inst_2971_);
                        v_string_3102_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                        crate::leanh::lean_inc_ref(v_string_3102_);
                        crate::leanh::lean_dec_ref_known(v_x_2973_, 1);
                        v___x_3103_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(
                            v_string_3102_,
                        );
                        v___x_3104_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3105_ = lean_mk_empty_array_with_capacity(v___x_3104_);
                        v___x_3106_ = lean_array_push(v___x_3105_, v___x_3103_);
                        v___x_3107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3107_, 0, v___x_3106_);
                        crate::leanh::lean_ctor_set(v___x_3107_, 1, v_a_2974_);
                        return v___x_3107_;
                    }
                    4 => {
                        crate::leanh::lean_dec_ref(v_x_2972_);
                        crate::leanh::lean_dec_ref(v_inst_2971_);
                        v_mode_3108_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_2973_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_mode_3108_ == 0 {
                            v_string_3109_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                            crate::leanh::lean_inc_ref(v_string_3109_);
                            crate::leanh::lean_dec_ref_known(v_x_2973_, 1);
                            v___x_3110_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__25;
                            v___x_3111_ = lean_string_append(v___x_3110_, v_string_3109_);
                            crate::leanh::lean_dec_ref(v_string_3109_);
                            v___x_3112_ = lean_string_append(v___x_3111_, v___x_3110_);
                            v___x_3113_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3114_ = lean_mk_empty_array_with_capacity(v___x_3113_);
                            v___x_3115_ = lean_array_push(v___x_3114_, v___x_3112_);
                            v___x_3116_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3116_, 0, v___x_3115_);
                            crate::leanh::lean_ctor_set(v___x_3116_, 1, v_a_2974_);
                            return v___x_3116_;
                        } else {
                            v_string_3117_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                            crate::leanh::lean_inc_ref(v_string_3117_);
                            crate::leanh::lean_dec_ref_known(v_x_2973_, 1);
                            v___x_3118_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__26;
                            v___x_3119_ = lean_string_append(v___x_3118_, v_string_3117_);
                            crate::leanh::lean_dec_ref(v_string_3117_);
                            v___x_3120_ = lean_string_append(v___x_3119_, v___x_3118_);
                            v___x_3121_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3122_ = lean_mk_empty_array_with_capacity(v___x_3121_);
                            v___x_3123_ = lean_array_push(v___x_3122_, v___x_3120_);
                            v___x_3124_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3124_, 0, v___x_3123_);
                            crate::leanh::lean_ctor_set(v___x_3124_, 1, v_a_2974_);
                            return v___x_3124_;
                        }
                    }
                    5 => {
                        crate::leanh::lean_dec_ref_known(v_x_2973_, 1);
                        crate::leanh::lean_dec_ref(v_x_2972_);
                        crate::leanh::lean_dec_ref(v_inst_2971_);
                        v___x_3125_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__27;
                        v___x_3126_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3126_, 0, v___x_3125_);
                        crate::leanh::lean_ctor_set(v___x_3126_, 1, v_a_2974_);
                        return v___x_3126_;
                    }
                    6 => {
                        v_inLink_3127_ = crate::leanh::lean_ctor_get_uint8(v_x_2972_, 2 as u32);
                        if v_inLink_3127_ == 0 {
                            v_content_3128_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                            crate::leanh::lean_inc_ref(v_content_3128_);
                            v_url_3129_ = crate::leanh::lean_ctor_get(v_x_2973_, 1);
                            crate::leanh::lean_inc_ref(v_url_3129_);
                            crate::leanh::lean_dec_ref_known(v_x_2973_, 2);
                            v_inEmph_3130_ = crate::leanh::lean_ctor_get_uint8(v_x_2972_, 0 as u32);
                            v_inBold_3131_ = crate::leanh::lean_ctor_get_uint8(v_x_2972_, 1 as u32);
                            v_isSharedCheck_3161_ =
                                (!crate::leanh::lean_is_exclusive(v_x_2972_)) as u8;
                            if v_isSharedCheck_3161_ == 0 {
                                v___x_3133_ = v_x_2972_;
                                v_isShared_3134_ = v_isSharedCheck_3161_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_x_2972_);
                                v___x_3133_ = crate::leanh::lean_box(0);
                                v_isShared_3134_ = v_isSharedCheck_3161_;
                                state = 17;
                                continue;
                            }
                        } else {
                            v_content_3162_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                            crate::leanh::lean_inc_ref(v_content_3162_);
                            crate::leanh::lean_dec_ref_known(v_x_2973_, 2);
                            v___x_3163_ = crate::leanh::lean_alloc_closure(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg as *mut core::ffi::c_void, 4, 2);
                            crate::leanh::lean_closure_set(v___x_3163_, 0, v_inst_2971_);
                            crate::leanh::lean_closure_set(v___x_3163_, 1, v_x_2972_);
                            v_sz_3164_ = lean_array_size(v_content_3162_);
                            v___x_3165_ = 0usize;
                            v___x_5248__overap_3166_ =
                                l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_2985_,
                                    v___x_3163_,
                                    v_sz_3164_,
                                    v___x_3165_,
                                    v_content_3162_,
                                );
                            v___x_3167_ =
                                crate::leanh::lean_apply_1(v___x_5248__overap_3166_, v_a_2974_);
                            v_fst_3168_ = crate::leanh::lean_ctor_get(v___x_3167_, 0);
                            v_snd_3169_ = crate::leanh::lean_ctor_get(v___x_3167_, 1);
                            v_isSharedCheck_3177_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3167_)) as u8;
                            if v_isSharedCheck_3177_ == 0 {
                                v___x_3171_ = v___x_3167_;
                                v_isShared_3172_ = v_isSharedCheck_3177_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_3169_);
                                crate::leanh::lean_inc(v_fst_3168_);
                                crate::leanh::lean_dec(v___x_3167_);
                                v___x_3171_ = crate::leanh::lean_box(0);
                                v_isShared_3172_ = v_isSharedCheck_3177_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                    7 => {
                        v_name_3178_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                        crate::leanh::lean_inc_ref(v_name_3178_);
                        v_content_3179_ = crate::leanh::lean_ctor_get(v_x_2973_, 1);
                        crate::leanh::lean_inc_ref(v_content_3179_);
                        crate::leanh::lean_dec_ref_known(v_x_2973_, 2);
                        v___x_3180_ = crate::leanh::lean_alloc_closure(
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg
                                as *mut core::ffi::c_void,
                            4,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___x_3180_, 0, v_inst_2971_);
                        crate::leanh::lean_closure_set(v___x_3180_, 1, v_x_2972_);
                        v_sz_3181_ = lean_array_size(v_content_3179_);
                        v___x_3182_ = 0usize;
                        v___x_5251__overap_3183_ =
                            l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_2985_,
                                v___x_3180_,
                                v_sz_3181_,
                                v___x_3182_,
                                v_content_3179_,
                            );
                        v___x_3184_ =
                            crate::leanh::lean_apply_1(v___x_5251__overap_3183_, v_a_2974_);
                        v_fst_3185_ = crate::leanh::lean_ctor_get(v___x_3184_, 0);
                        v_snd_3186_ = crate::leanh::lean_ctor_get(v___x_3184_, 1);
                        v_isSharedCheck_3206_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3184_)) as u8;
                        if v_isSharedCheck_3206_ == 0 {
                            v___x_3188_ = v___x_3184_;
                            v_isShared_3189_ = v_isSharedCheck_3206_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3186_);
                            crate::leanh::lean_inc(v_fst_3185_);
                            crate::leanh::lean_dec(v___x_3184_);
                            v___x_3188_ = crate::leanh::lean_box(0);
                            v_isShared_3189_ = v_isSharedCheck_3206_;
                            state = 23;
                            continue;
                        }
                    }
                    8 => {
                        crate::leanh::lean_dec_ref(v_x_2972_);
                        crate::leanh::lean_dec_ref(v_inst_2971_);
                        v_alt_3207_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                        crate::leanh::lean_inc_ref(v_alt_3207_);
                        v_url_3208_ = crate::leanh::lean_ctor_get(v_x_2973_, 1);
                        crate::leanh::lean_inc_ref(v_url_3208_);
                        crate::leanh::lean_dec_ref_known(v_x_2973_, 2);
                        v___x_3209_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__34;
                        v___x_3210_ =
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_3207_);
                        crate::leanh::lean_dec_ref(v_alt_3207_);
                        v___x_3211_ = lean_string_append(v___x_3209_, v___x_3210_);
                        crate::leanh::lean_dec_ref(v___x_3210_);
                        v___x_3212_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30;
                        v___x_3213_ = lean_string_append(v___x_3211_, v___x_3212_);
                        v___x_3214_ = lean_string_append(v___x_3213_, v_url_3208_);
                        crate::leanh::lean_dec_ref(v_url_3208_);
                        v___x_3215_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31;
                        v___x_3216_ = lean_string_append(v___x_3214_, v___x_3215_);
                        v___x_3217_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3218_ = lean_mk_empty_array_with_capacity(v___x_3217_);
                        v___x_3219_ = lean_array_push(v___x_3218_, v___x_3216_);
                        v___x_3220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3220_, 0, v___x_3219_);
                        crate::leanh::lean_ctor_set(v___x_3220_, 1, v_a_2974_);
                        return v___x_3220_;
                    }
                    9 => {
                        v_content_3221_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                        crate::leanh::lean_inc_ref(v_content_3221_);
                        crate::leanh::lean_dec_ref_known(v_x_2973_, 1);
                        v___x_3222_ = crate::leanh::lean_alloc_closure(
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg
                                as *mut core::ffi::c_void,
                            4,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___x_3222_, 0, v_inst_2971_);
                        crate::leanh::lean_closure_set(v___x_3222_, 1, v_x_2972_);
                        v_sz_3223_ = lean_array_size(v_content_3221_);
                        v___x_3224_ = 0usize;
                        v___x_5254__overap_3225_ =
                            l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_2985_,
                                v___x_3222_,
                                v_sz_3223_,
                                v___x_3224_,
                                v_content_3221_,
                            );
                        v___x_3226_ =
                            crate::leanh::lean_apply_1(v___x_5254__overap_3225_, v_a_2974_);
                        v_fst_3227_ = crate::leanh::lean_ctor_get(v___x_3226_, 0);
                        v_snd_3228_ = crate::leanh::lean_ctor_get(v___x_3226_, 1);
                        v_isSharedCheck_3236_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3226_)) as u8;
                        if v_isSharedCheck_3236_ == 0 {
                            v___x_3230_ = v___x_3226_;
                            v_isShared_3231_ = v_isSharedCheck_3236_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3228_);
                            crate::leanh::lean_inc(v_fst_3227_);
                            crate::leanh::lean_dec(v___x_3226_);
                            v___x_3230_ = crate::leanh::lean_box(0);
                            v_isShared_3231_ = v_isSharedCheck_3236_;
                            state = 25;
                            continue;
                        }
                    }
                    _ => {
                        v_container_3237_ = crate::leanh::lean_ctor_get(v_x_2973_, 0);
                        crate::leanh::lean_inc(v_container_3237_);
                        v_content_3238_ = crate::leanh::lean_ctor_get(v_x_2973_, 1);
                        crate::leanh::lean_inc_ref(v_content_3238_);
                        crate::leanh::lean_dec_ref_known(v_x_2973_, 2);
                        crate::leanh::lean_inc_ref(v_inst_2971_);
                        v___x_3239_ = crate::leanh::lean_alloc_closure(
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg
                                as *mut core::ffi::c_void,
                            4,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___x_3239_, 0, v_inst_2971_);
                        crate::leanh::lean_closure_set(v___x_3239_, 1, v_x_2972_);
                        v___x_3240_ = crate::leanh::lean_apply_4(
                            v_inst_2971_,
                            v___x_3239_,
                            v_container_3237_,
                            v_content_3238_,
                            v_a_2974_,
                        );
                        return v___x_3240_;
                    }
                }
            }
            1 => {
                v___x_2978_ = l_Lean_Doc_joinInlines(v_pieces_2976_);
                crate::leanh::lean_dec_ref(v_pieces_2976_);
                v___x_2979_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2979_, 0, v___x_2978_);
                crate::leanh::lean_ctor_set(v___x_2979_, 1, v___y_2977_);
                return v___x_2979_;
            }
            2 => {
                v___x_2983_ = l_Lean_Doc_joinInlines(v_pieces_2981_);
                crate::leanh::lean_dec_ref(v_pieces_2981_);
                v___x_2984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2984_, 0, v___x_2983_);
                crate::leanh::lean_ctor_set(v___x_2984_, 1, v___y_2982_);
                return v___x_2984_;
            }
            3 => {
                if v_isShared_2995_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2994_, 9);
                    v___x_2997_ = v___x_2994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3045_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_content_2992_);
                    v___x_2997_ = v_reuseFailAlloc_3045_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2998_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_2997_);
                v_snd_2999_ = crate::leanh::lean_ctor_get(v___x_2998_, 1);
                crate::leanh::lean_inc(v_snd_2999_);
                v_fst_3000_ = crate::leanh::lean_ctor_get(v___x_2998_, 0);
                crate::leanh::lean_inc(v_fst_3000_);
                crate::leanh::lean_dec_ref(v___x_2998_);
                v_fst_3001_ = crate::leanh::lean_ctor_get(v_snd_2999_, 0);
                crate::leanh::lean_inc(v_fst_3001_);
                v_snd_3002_ = crate::leanh::lean_ctor_get(v_snd_2999_, 1);
                crate::leanh::lean_inc(v_snd_3002_);
                crate::leanh::lean_dec(v_snd_2999_);
                v_inEmph_3013_ = crate::leanh::lean_ctor_get_uint8(v_x_2972_, 0 as u32);
                v_inBold_3014_ = crate::leanh::lean_ctor_get_uint8(v_x_2972_, 1 as u32);
                v_inLink_3015_ = crate::leanh::lean_ctor_get_uint8(v_x_2972_, 2 as u32);
                v_isSharedCheck_3044_ = (!crate::leanh::lean_is_exclusive(v_x_2972_)) as u8;
                if v_isSharedCheck_3044_ == 0 {
                    v___x_3017_ = v_x_2972_;
                    v_isShared_3018_ = v_isSharedCheck_3044_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_2972_);
                    v___x_3017_ = crate::leanh::lean_box(0);
                    v_isShared_3018_ = v_isSharedCheck_3044_;
                    state = 6;
                    continue;
                }
            }
            5 => {
                v___x_3006_ = lean_string_utf8_byte_size(v_snd_3002_);
                v___x_3007_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3008_ = lean_nat_dec_eq(v___x_3006_, v___x_3007_);
                if v___x_3008_ == 0 {
                    v___x_3009_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3010_ = lean_mk_empty_array_with_capacity(v___x_3009_);
                    v___x_3011_ = lean_array_push(v___x_3010_, v_snd_3002_);
                    v___x_3012_ = lean_array_push(v_pieces_3004_, v___x_3011_);
                    v_pieces_2981_ = v___x_3012_;
                    v___y_2982_ = v___y_3005_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_3002_);
                    v_pieces_2981_ = v_pieces_3004_;
                    v___y_2982_ = v___y_3005_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_3019_ = 1;
                if v_isShared_3018_ == 0 {
                    v___x_3021_ = v___x_3017_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3043_ = crate::leanh::lean_alloc_ctor(0, 0, (3) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3043_,
                        1 as u32,
                        v_inBold_3014_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3043_,
                        2 as u32,
                        v_inLink_3015_,
                    );
                    v___x_3021_ = v_reuseFailAlloc_3043_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_ctor_set_uint8(v___x_3021_, 0 as u32, v___x_3019_);
                v___x_3022_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(
                        v_inst_2971_,
                        v___x_3021_,
                        v_fst_3001_,
                        v_a_2974_,
                    );
                v_fst_3023_ = crate::leanh::lean_ctor_get(v___x_3022_, 0);
                crate::leanh::lean_inc(v_fst_3023_);
                v_snd_3024_ = crate::leanh::lean_ctor_get(v___x_3022_, 1);
                crate::leanh::lean_inc(v_snd_3024_);
                crate::leanh::lean_dec_ref(v___x_3022_);
                v___x_3035_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3036_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22;
                v___x_3037_ = lean_string_utf8_byte_size(v_fst_3000_);
                v___x_3038_ = lean_nat_dec_eq(v___x_3037_, v___x_3035_);
                if v___x_3038_ == 0 {
                    v___x_3039_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3040_ = lean_mk_empty_array_with_capacity(v___x_3039_);
                    v___x_3041_ = lean_array_push(v___x_3040_, v_fst_3000_);
                    v___x_3042_ = lean_array_push(v___x_3036_, v___x_3041_);
                    v_pieces_3032_ = v___x_3042_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3000_);
                    v_pieces_3032_ = v___x_3036_;
                    state = 9;
                    continue;
                }
            }
            8 => {
                v___x_3028_ = lean_array_push(v_pieces_3026_, v_fst_3023_);
                if v_inEmph_3013_ == 0 {
                    v___x_3029_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21;
                    v___x_3030_ = lean_array_push(v___x_3028_, v___x_3029_);
                    v_pieces_3004_ = v___x_3030_;
                    v___y_3005_ = v___y_3027_;
                    state = 5;
                    continue;
                } else {
                    v_pieces_3004_ = v___x_3028_;
                    v___y_3005_ = v___y_3027_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                if v_inEmph_3013_ == 0 {
                    v___x_3033_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__21;
                    v___x_3034_ = lean_array_push(v_pieces_3032_, v___x_3033_);
                    v_pieces_3026_ = v___x_3034_;
                    v___y_3027_ = v_snd_3024_;
                    state = 8;
                    continue;
                } else {
                    v_pieces_3026_ = v_pieces_3032_;
                    v___y_3027_ = v_snd_3024_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v_isShared_3050_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3049_, 9);
                    v___x_3052_ = v___x_3049_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_content_3047_);
                    v___x_3052_ = v_reuseFailAlloc_3100_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3053_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_trim___redArg(v___x_3052_);
                v_snd_3054_ = crate::leanh::lean_ctor_get(v___x_3053_, 1);
                crate::leanh::lean_inc(v_snd_3054_);
                v_fst_3055_ = crate::leanh::lean_ctor_get(v___x_3053_, 0);
                crate::leanh::lean_inc(v_fst_3055_);
                crate::leanh::lean_dec_ref(v___x_3053_);
                v_fst_3056_ = crate::leanh::lean_ctor_get(v_snd_3054_, 0);
                crate::leanh::lean_inc(v_fst_3056_);
                v_snd_3057_ = crate::leanh::lean_ctor_get(v_snd_3054_, 1);
                crate::leanh::lean_inc(v_snd_3057_);
                crate::leanh::lean_dec(v_snd_3054_);
                v_inEmph_3068_ = crate::leanh::lean_ctor_get_uint8(v_x_2972_, 0 as u32);
                v_inBold_3069_ = crate::leanh::lean_ctor_get_uint8(v_x_2972_, 1 as u32);
                v_inLink_3070_ = crate::leanh::lean_ctor_get_uint8(v_x_2972_, 2 as u32);
                v_isSharedCheck_3099_ = (!crate::leanh::lean_is_exclusive(v_x_2972_)) as u8;
                if v_isSharedCheck_3099_ == 0 {
                    v___x_3072_ = v_x_2972_;
                    v_isShared_3073_ = v_isSharedCheck_3099_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_2972_);
                    v___x_3072_ = crate::leanh::lean_box(0);
                    v_isShared_3073_ = v_isSharedCheck_3099_;
                    state = 13;
                    continue;
                }
            }
            12 => {
                v___x_3061_ = lean_string_utf8_byte_size(v_snd_3057_);
                v___x_3062_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3063_ = lean_nat_dec_eq(v___x_3061_, v___x_3062_);
                if v___x_3063_ == 0 {
                    v___x_3064_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3065_ = lean_mk_empty_array_with_capacity(v___x_3064_);
                    v___x_3066_ = lean_array_push(v___x_3065_, v_snd_3057_);
                    v___x_3067_ = lean_array_push(v_pieces_3059_, v___x_3066_);
                    v_pieces_2976_ = v___x_3067_;
                    v___y_2977_ = v___y_3060_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_3057_);
                    v_pieces_2976_ = v_pieces_3059_;
                    v___y_2977_ = v___y_3060_;
                    state = 1;
                    continue;
                }
            }
            13 => {
                v___x_3074_ = 1;
                if v_isShared_3073_ == 0 {
                    v___x_3076_ = v___x_3072_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = crate::leanh::lean_alloc_ctor(0, 0, (3) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3098_,
                        0 as u32,
                        v_inEmph_3068_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3098_,
                        2 as u32,
                        v_inLink_3070_,
                    );
                    v___x_3076_ = v_reuseFailAlloc_3098_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(v___x_3076_, 1 as u32, v___x_3074_);
                v___x_3077_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(
                        v_inst_2971_,
                        v___x_3076_,
                        v_fst_3056_,
                        v_a_2974_,
                    );
                v_fst_3078_ = crate::leanh::lean_ctor_get(v___x_3077_, 0);
                crate::leanh::lean_inc(v_fst_3078_);
                v_snd_3079_ = crate::leanh::lean_ctor_get(v___x_3077_, 1);
                crate::leanh::lean_inc(v_snd_3079_);
                crate::leanh::lean_dec_ref(v___x_3077_);
                v___x_3090_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3091_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22;
                v___x_3092_ = lean_string_utf8_byte_size(v_fst_3055_);
                v___x_3093_ = lean_nat_dec_eq(v___x_3092_, v___x_3090_);
                if v___x_3093_ == 0 {
                    v___x_3094_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3095_ = lean_mk_empty_array_with_capacity(v___x_3094_);
                    v___x_3096_ = lean_array_push(v___x_3095_, v_fst_3055_);
                    v___x_3097_ = lean_array_push(v___x_3091_, v___x_3096_);
                    v_pieces_3087_ = v___x_3097_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3055_);
                    v_pieces_3087_ = v___x_3091_;
                    state = 16;
                    continue;
                }
            }
            15 => {
                v___x_3083_ = lean_array_push(v_pieces_3081_, v_fst_3078_);
                if v_inBold_3069_ == 0 {
                    v___x_3084_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24;
                    v___x_3085_ = lean_array_push(v___x_3083_, v___x_3084_);
                    v_pieces_3059_ = v___x_3085_;
                    v___y_3060_ = v___y_3082_;
                    state = 12;
                    continue;
                } else {
                    v_pieces_3059_ = v___x_3083_;
                    v___y_3060_ = v___y_3082_;
                    state = 12;
                    continue;
                }
            }
            16 => {
                if v_inBold_3069_ == 0 {
                    v___x_3088_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__24;
                    v___x_3089_ = lean_array_push(v_pieces_3087_, v___x_3088_);
                    v_pieces_3081_ = v___x_3089_;
                    v___y_3082_ = v_snd_3079_;
                    state = 15;
                    continue;
                } else {
                    v_pieces_3081_ = v_pieces_3087_;
                    v___y_3082_ = v_snd_3079_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                v___x_3135_ = 1;
                if v_isShared_3134_ == 0 {
                    v___x_3137_ = v___x_3133_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = crate::leanh::lean_alloc_ctor(0, 0, (3) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3160_,
                        0 as u32,
                        v_inEmph_3130_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3160_,
                        1 as u32,
                        v_inBold_3131_,
                    );
                    v___x_3137_ = v_reuseFailAlloc_3160_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                crate::leanh::lean_ctor_set_uint8(v___x_3137_, 2 as u32, v___x_3135_);
                v___x_3138_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3138_, 0, v_content_3128_);
                v___x_3139_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(
                        v_inst_2971_,
                        v___x_3137_,
                        v___x_3138_,
                        v_a_2974_,
                    );
                v_fst_3140_ = crate::leanh::lean_ctor_get(v___x_3139_, 0);
                v_snd_3141_ = crate::leanh::lean_ctor_get(v___x_3139_, 1);
                v_isSharedCheck_3159_ = (!crate::leanh::lean_is_exclusive(v___x_3139_)) as u8;
                if v_isSharedCheck_3159_ == 0 {
                    v___x_3143_ = v___x_3139_;
                    v_isShared_3144_ = v_isSharedCheck_3159_;
                    state = 19;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3141_);
                    crate::leanh::lean_inc(v_fst_3140_);
                    crate::leanh::lean_dec(v___x_3139_);
                    v___x_3143_ = crate::leanh::lean_box(0);
                    v_isShared_3144_ = v_isSharedCheck_3159_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_3145_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3146_ = lean_mk_empty_array_with_capacity(v___x_3145_);
                v___x_3147_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__30;
                v___x_3148_ = lean_string_append(v___x_3147_, v_url_3129_);
                crate::leanh::lean_dec_ref(v_url_3129_);
                v___x_3149_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__31;
                v___x_3150_ = lean_string_append(v___x_3148_, v___x_3149_);
                v___x_3151_ = lean_array_push(v___x_3146_, v___x_3150_);
                v___x_3152_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32), core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32_once), _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__32);
                v___x_3153_ = lean_array_push(v___x_3152_, v_fst_3140_);
                v___x_3154_ = lean_array_push(v___x_3153_, v___x_3151_);
                v___x_3155_ = l_Lean_Doc_joinInlines(v___x_3154_);
                crate::leanh::lean_dec_ref(v___x_3154_);
                if v_isShared_3144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3143_, 0, v___x_3155_);
                    v___x_3157_ = v___x_3143_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_snd_3141_);
                    v___x_3157_ = v_reuseFailAlloc_3158_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3157_;
            }
            21 => {
                v___x_3173_ = l_Lean_Doc_joinInlines(v_fst_3168_);
                crate::leanh::lean_dec(v_fst_3168_);
                if v_isShared_3172_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3171_, 0, v___x_3173_);
                    v___x_3175_ = v___x_3171_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_snd_3169_);
                    v___x_3175_ = v_reuseFailAlloc_3176_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3175_;
            }
            23 => {
                v___x_3190_ = l_Lean_Doc_MarkdownM_run_x27___closed__1;
                v___x_3191_ = l_Lean_Doc_joinInlines(v_fst_3185_);
                crate::leanh::lean_dec(v_fst_3185_);
                v___x_3192_ = lean_array_to_list(v___x_3191_);
                v___x_3193_ = l_String_intercalate(v___x_3190_, v___x_3192_);
                crate::leanh::lean_inc_ref(v_name_3178_);
                if v_isShared_3189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3188_, 1, v___x_3193_);
                    crate::leanh::lean_ctor_set(v___x_3188_, 0, v_name_3178_);
                    v___x_3195_ = v___x_3188_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_name_3178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___x_3193_);
                    v___x_3195_ = v_reuseFailAlloc_3205_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_3196_ = lean_array_push(v_snd_3186_, v___x_3195_);
                v___x_3197_ =
                    l_List_mapTR_loop___at___00Lean_Doc_MarkdownM_run_x27_spec__0___closed__0;
                v___x_3198_ = lean_string_append(v___x_3197_, v_name_3178_);
                crate::leanh::lean_dec_ref(v_name_3178_);
                v___x_3199_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__33;
                v___x_3200_ = lean_string_append(v___x_3198_, v___x_3199_);
                v___x_3201_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3202_ = lean_mk_empty_array_with_capacity(v___x_3201_);
                v___x_3203_ = lean_array_push(v___x_3202_, v___x_3200_);
                v___x_3204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3204_, 0, v___x_3203_);
                crate::leanh::lean_ctor_set(v___x_3204_, 1, v___x_3196_);
                return v___x_3204_;
            }
            25 => {
                v___x_3232_ = l_Lean_Doc_joinInlines(v_fst_3227_);
                crate::leanh::lean_dec(v_fst_3227_);
                if v_isShared_3231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3230_, 0, v___x_3232_);
                    v___x_3234_ = v___x_3230_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_snd_3228_);
                    v___x_3234_ = v_reuseFailAlloc_3235_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown(
    mut v_i_3241_: *mut crate::leanh::LeanObject,
    mut v_inst_3242_: *mut crate::leanh::LeanObject,
    mut v_x_3243_: *mut crate::leanh::LeanObject,
    mut v_x_3244_: *mut crate::leanh::LeanObject,
    mut v_a_3245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3246_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(
        v_inst_3242_,
        v_x_3243_,
        v_x_3244_,
        v_a_3245_,
    );
    return v___x_3246_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1___redArg(
    mut v_inst_3247_: *mut crate::leanh::LeanObject,
    mut v_a_3248_: *mut crate::leanh::LeanObject,
    mut v_a_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3250_ = l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0;
    v___x_3251_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(
        v_inst_3247_,
        v___x_3250_,
        v_a_3248_,
        v_a_3249_,
    );
    return v___x_3251_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1(
    mut v_i_3252_: *mut crate::leanh::LeanObject,
    mut v_inst_3253_: *mut crate::leanh::LeanObject,
    mut v_a_3254_: *mut crate::leanh::LeanObject,
    mut v_a_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0;
    v___x_3257_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(
        v_inst_3253_,
        v___x_3256_,
        v_a_3254_,
        v_a_3255_,
    );
    return v___x_3257_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___redArg(
    mut v_inst_3258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3259_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3259_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3259_, 1, v_inst_3258_);
    return v___x_3259_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownInlineOfMarkdownInline(
    mut v_i_3260_: *mut crate::leanh::LeanObject,
    mut v_inst_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3262_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3262_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3262_, 1, v_inst_3261_);
    return v___x_3262_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(
    mut v___x_3263_: u32,
    mut v_s_3264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3265_ = lean_string_push(v_s_3264_, v___x_3263_);
    return v___x_3265_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed(
    mut v___x_3266_: *mut crate::leanh::LeanObject,
    mut v_s_3267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3198__boxed_3268_: u32 = 0;
    let mut v_res_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3198__boxed_3268_ = crate::leanh::lean_unbox_uint32(v___x_3266_);
    crate::leanh::lean_dec(v___x_3266_);
    v_res_3269_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1(
        v___x_3198__boxed_3268_,
        v_s_3267_,
    );
    return v_res_3269_;
}
pub unsafe fn _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3273_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1;
    v___f_3274_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3274_, 0, v___x_3273_);
    return v___f_3274_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(
    mut v_inst_3275_: *mut crate::leanh::LeanObject,
    mut v_inst_3276_: *mut crate::leanh::LeanObject,
    mut v___x_3277_: *mut crate::leanh::LeanObject,
    mut v___x_3278_: *mut crate::leanh::LeanObject,
    mut v_a_3279_: *mut crate::leanh::LeanObject,
    mut v_x_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3284_: usize = 0;
    let mut v___x_3285_: usize = 0;
    let mut v___x_3142__overap_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v_fst_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3297_: u8 = 0;
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3316_: u8 = 0;
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3283_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3283_, 0, v_inst_3275_);
                crate::leanh::lean_closure_set(v___x_3283_, 1, v_inst_3276_);
                v_sz_3284_ = lean_array_size(v_a_3279_);
                v___x_3285_ = 0usize;
                v___x_3142__overap_3286_ =
                    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3277_,
                        v___x_3283_,
                        v_sz_3284_,
                        v___x_3285_,
                        v_a_3279_,
                    );
                v___x_3287_ = crate::leanh::lean_apply_1(v___x_3142__overap_3286_, v___y_3282_);
                v_fst_3288_ = crate::leanh::lean_ctor_get(v___x_3287_, 0);
                v_snd_3289_ = crate::leanh::lean_ctor_get(v___x_3287_, 1);
                v_isSharedCheck_3317_ = (!crate::leanh::lean_is_exclusive(v___x_3287_)) as u8;
                if v_isSharedCheck_3317_ == 0 {
                    v___x_3291_ = v___x_3287_;
                    v_isShared_3292_ = v_isSharedCheck_3317_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3289_);
                    crate::leanh::lean_inc(v_fst_3288_);
                    crate::leanh::lean_dec(v___x_3287_);
                    v___x_3291_ = crate::leanh::lean_box(0);
                    v_isShared_3292_ = v_isSharedCheck_3317_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3293_ = crate::leanh::lean_ctor_get(v___y_3281_, 0);
                v_snd_3294_ = crate::leanh::lean_ctor_get(v___y_3281_, 1);
                v_isSharedCheck_3316_ = (!crate::leanh::lean_is_exclusive(v___y_3281_)) as u8;
                if v_isSharedCheck_3316_ == 0 {
                    v___x_3296_ = v___y_3281_;
                    v_isShared_3297_ = v_isSharedCheck_3316_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3294_);
                    crate::leanh::lean_inc(v_fst_3293_);
                    crate::leanh::lean_dec(v___y_3281_);
                    v___x_3296_ = crate::leanh::lean_box(0);
                    v_isShared_3297_ = v_isSharedCheck_3316_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_snd_3294_);
                v___x_3298_ = l_Nat_reprFast(v_snd_3294_);
                v___x_3299_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__0;
                v___x_3300_ = lean_string_append(v___x_3298_, v___x_3299_);
                v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0;
                v___f_3302_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1_once), _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___closed__1);
                v___x_3303_ = lean_string_utf8_byte_size(v___x_3300_);
                v___x_3304_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(
                    crate::leanh::lean_box(0),
                    v___f_3302_,
                    v___x_3303_,
                    v___x_3301_,
                );
                v___x_3305_ = l_Lean_Doc_joinBlocks(v_fst_3288_);
                crate::leanh::lean_dec(v_fst_3288_);
                v___x_3306_ = l_Lean_Doc_prefixListLines(v___x_3300_, v___x_3304_, v___x_3305_);
                crate::leanh::lean_dec_ref(v___x_3305_);
                v___x_3307_ = lean_array_push(v_fst_3293_, v___x_3306_);
                v___x_3308_ = lean_nat_add(v_snd_3294_, v___x_3278_);
                crate::leanh::lean_dec(v_snd_3294_);
                if v_isShared_3297_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3296_, 1, v___x_3308_);
                    crate::leanh::lean_ctor_set(v___x_3296_, 0, v___x_3307_);
                    v___x_3310_ = v___x_3296_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3315_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3315_, 1, v___x_3308_);
                    v___x_3310_ = v_reuseFailAlloc_3315_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3311_, 0, v___x_3310_);
                if v_isShared_3292_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3291_, 0, v___x_3311_);
                    v___x_3313_ = v___x_3291_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_snd_3289_);
                    v___x_3313_ = v_reuseFailAlloc_3314_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed(
    mut v_inst_3318_: *mut crate::leanh::LeanObject,
    mut v_inst_3319_: *mut crate::leanh::LeanObject,
    mut v___x_3320_: *mut crate::leanh::LeanObject,
    mut v___x_3321_: *mut crate::leanh::LeanObject,
    mut v_a_3322_: *mut crate::leanh::LeanObject,
    mut v_x_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3326_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2(
        v_inst_3318_,
        v_inst_3319_,
        v___x_3320_,
        v___x_3321_,
        v_a_3322_,
        v_x_3323_,
        v___y_3324_,
        v___y_3325_,
    );
    crate::leanh::lean_dec(v___x_3321_);
    return v_res_3326_;
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3(
    mut v_inst_3332_: *mut crate::leanh::LeanObject,
    mut v_inst_3333_: *mut crate::leanh::LeanObject,
    mut v___x_3334_: *mut crate::leanh::LeanObject,
    mut v_item_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_desc_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3345_: usize = 0;
    let mut v___x_3346_: usize = 0;
    let mut v___x_3172__overap_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3353_: u8 = 0;
    let mut v___y_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3337_ = l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0;
                v_term_3338_ = crate::leanh::lean_ctor_get(v_item_3335_, 0);
                crate::leanh::lean_inc_ref(v_term_3338_);
                v_desc_3339_ = crate::leanh::lean_ctor_get(v_item_3335_, 1);
                crate::leanh::lean_inc_ref_n(v_desc_3339_, 2);
                crate::leanh::lean_dec_ref(v_item_3335_);
                v___x_3340_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3340_, 0, v_term_3338_);
                crate::leanh::lean_inc_ref(v_inst_3332_);
                v___x_3341_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(
                        v_inst_3332_,
                        v___x_3337_,
                        v___x_3340_,
                        v___y_3336_,
                    );
                v_fst_3342_ = crate::leanh::lean_ctor_get(v___x_3341_, 0);
                crate::leanh::lean_inc(v_fst_3342_);
                v_snd_3343_ = crate::leanh::lean_ctor_get(v___x_3341_, 1);
                crate::leanh::lean_inc(v_snd_3343_);
                crate::leanh::lean_dec_ref(v___x_3341_);
                v___x_3344_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3344_, 0, v_inst_3332_);
                crate::leanh::lean_closure_set(v___x_3344_, 1, v_inst_3333_);
                v_sz_3345_ = lean_array_size(v_desc_3339_);
                v___x_3346_ = 0usize;
                v___x_3172__overap_3347_ =
                    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3334_,
                        v___x_3344_,
                        v_sz_3345_,
                        v___x_3346_,
                        v_desc_3339_,
                    );
                v___x_3348_ = crate::leanh::lean_apply_1(v___x_3172__overap_3347_, v_snd_3343_);
                v_fst_3349_ = crate::leanh::lean_ctor_get(v___x_3348_, 0);
                v_snd_3350_ = crate::leanh::lean_ctor_get(v___x_3348_, 1);
                v_isSharedCheck_3377_ = (!crate::leanh::lean_is_exclusive(v___x_3348_)) as u8;
                if v_isSharedCheck_3377_ == 0 {
                    v___x_3352_ = v___x_3348_;
                    v_isShared_3353_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3350_);
                    crate::leanh::lean_inc(v_fst_3349_);
                    crate::leanh::lean_dec(v___x_3348_);
                    v___x_3352_ = crate::leanh::lean_box(0);
                    v_isShared_3353_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3362_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3363_ = lean_mk_empty_array_with_capacity(v___x_3362_);
                v___x_3364_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3___closed__1;
                v___x_3365_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3366_ = lean_mk_empty_array_with_capacity(v___x_3365_);
                v___x_3367_ = lean_array_push(v___x_3366_, v_fst_3342_);
                v___x_3368_ = lean_array_push(v___x_3367_, v___x_3364_);
                v___x_3369_ = l_Lean_Doc_joinInlines(v___x_3368_);
                crate::leanh::lean_dec_ref(v___x_3368_);
                v___x_3370_ = lean_array_get_size(v_desc_3339_);
                crate::leanh::lean_dec_ref(v_desc_3339_);
                v___x_3371_ = lean_nat_dec_le(v___x_3370_, v___x_3362_);
                if v___x_3371_ == 0 {
                    v___x_3372_ = lean_array_push(v___x_3363_, v___x_3369_);
                    v___x_3373_ = l_Array_append___redArg(v___x_3372_, v_fst_3349_);
                    crate::leanh::lean_dec(v_fst_3349_);
                    v___x_3374_ = l_Lean_Doc_joinBlocks(v___x_3373_);
                    crate::leanh::lean_dec_ref(v___x_3373_);
                    v___y_3355_ = v___x_3374_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_3363_);
                    v___x_3375_ = l_Lean_Doc_joinBlocks(v_fst_3349_);
                    crate::leanh::lean_dec(v_fst_3349_);
                    v___x_3376_ = l_Array_append___redArg(v___x_3369_, v___x_3375_);
                    crate::leanh::lean_dec_ref(v___x_3375_);
                    v___y_3355_ = v___x_3376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3356_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0;
                v___x_3357_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1;
                v___x_3358_ = l_Lean_Doc_prefixListLines(v___x_3356_, v___x_3357_, v___y_3355_);
                crate::leanh::lean_dec_ref(v___y_3355_);
                if v_isShared_3353_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3358_);
                    v___x_3360_ = v___x_3352_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_snd_3350_);
                    v___x_3360_ = v_reuseFailAlloc_3361_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(
    mut v_inst_3379_: *mut crate::leanh::LeanObject,
    mut v_inst_3380_: *mut crate::leanh::LeanObject,
    mut v_x_3381_: *mut crate::leanh::LeanObject,
    mut v_a_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contents_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3387_: u8 = 0;
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3393_: u8 = 0;
    let mut v_content_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3399_: usize = 0;
    let mut v___x_3400_: usize = 0;
    let mut v___x_3079__overap_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3407_: u8 = 0;
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3412_: u8 = 0;
    let mut v_start_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v_out_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3425_: usize = 0;
    let mut v___x_3426_: usize = 0;
    let mut v___x_2973__overap_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3434_: u8 = 0;
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3439_: u8 = 0;
    let mut v_unused_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: u8 = 0;
    let mut v_isSharedCheck_3444_: u8 = 0;
    let mut v_items_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3447_: usize = 0;
    let mut v___x_3448_: usize = 0;
    let mut v___x_3085__overap_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3455_: u8 = 0;
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3460_: u8 = 0;
    let mut v_items_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3463_: usize = 0;
    let mut v___x_3464_: usize = 0;
    let mut v___x_3088__overap_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v_content_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3481_: usize = 0;
    let mut v___x_3482_: usize = 0;
    let mut v___x_3091__overap_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3494_: u8 = 0;
    let mut v_container_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3383_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19;
                match crate::leanh::lean_obj_tag(v_x_3381_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_inst_3380_);
                        v_contents_3384_ = crate::leanh::lean_ctor_get(v_x_3381_, 0);
                        v_isSharedCheck_3393_ = (!crate::leanh::lean_is_exclusive(v_x_3381_)) as u8;
                        if v_isSharedCheck_3393_ == 0 {
                            v___x_3386_ = v_x_3381_;
                            v_isShared_3387_ = v_isSharedCheck_3393_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_contents_3384_);
                            crate::leanh::lean_dec(v_x_3381_);
                            v___x_3386_ = crate::leanh::lean_box(0);
                            v_isShared_3387_ = v_isSharedCheck_3393_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_inst_3380_);
                        crate::leanh::lean_dec_ref(v_inst_3379_);
                        v_content_3394_ = crate::leanh::lean_ctor_get(v_x_3381_, 0);
                        crate::leanh::lean_inc_ref(v_content_3394_);
                        crate::leanh::lean_dec_ref_known(v_x_3381_, 1);
                        v___x_3395_ =
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(
                                v_content_3394_,
                            );
                        v___x_3396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3396_, 0, v___x_3395_);
                        crate::leanh::lean_ctor_set(v___x_3396_, 1, v_a_3382_);
                        return v___x_3396_;
                    }
                    2 => {
                        v_items_3397_ = crate::leanh::lean_ctor_get(v_x_3381_, 0);
                        crate::leanh::lean_inc_ref(v_items_3397_);
                        crate::leanh::lean_dec_ref_known(v_x_3381_, 1);
                        v___f_3398_ = crate::leanh::lean_alloc_closure(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0 as *mut core::ffi::c_void, 5, 3);
                        crate::leanh::lean_closure_set(v___f_3398_, 0, v_inst_3379_);
                        crate::leanh::lean_closure_set(v___f_3398_, 1, v_inst_3380_);
                        crate::leanh::lean_closure_set(v___f_3398_, 2, v___x_3383_);
                        v_sz_3399_ = lean_array_size(v_items_3397_);
                        v___x_3400_ = 0usize;
                        v___x_3079__overap_3401_ =
                            l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_3383_,
                                v___f_3398_,
                                v_sz_3399_,
                                v___x_3400_,
                                v_items_3397_,
                            );
                        v___x_3402_ =
                            crate::leanh::lean_apply_1(v___x_3079__overap_3401_, v_a_3382_);
                        v_fst_3403_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                        v_snd_3404_ = crate::leanh::lean_ctor_get(v___x_3402_, 1);
                        v_isSharedCheck_3412_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3402_)) as u8;
                        if v_isSharedCheck_3412_ == 0 {
                            v___x_3406_ = v___x_3402_;
                            v_isShared_3407_ = v_isSharedCheck_3412_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3404_);
                            crate::leanh::lean_inc(v_fst_3403_);
                            crate::leanh::lean_dec(v___x_3402_);
                            v___x_3406_ = crate::leanh::lean_box(0);
                            v_isShared_3407_ = v_isSharedCheck_3412_;
                            state = 3;
                            continue;
                        }
                    }
                    3 => {
                        v_start_3413_ = crate::leanh::lean_ctor_get(v_x_3381_, 0);
                        v_items_3414_ = crate::leanh::lean_ctor_get(v_x_3381_, 1);
                        v_isSharedCheck_3444_ = (!crate::leanh::lean_is_exclusive(v_x_3381_)) as u8;
                        if v_isSharedCheck_3444_ == 0 {
                            v___x_3416_ = v_x_3381_;
                            v_isShared_3417_ = v_isSharedCheck_3444_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_items_3414_);
                            crate::leanh::lean_inc(v_start_3413_);
                            crate::leanh::lean_dec(v_x_3381_);
                            v___x_3416_ = crate::leanh::lean_box(0);
                            v_isShared_3417_ = v_isSharedCheck_3444_;
                            state = 5;
                            continue;
                        }
                    }
                    4 => {
                        v_items_3445_ = crate::leanh::lean_ctor_get(v_x_3381_, 0);
                        crate::leanh::lean_inc_ref(v_items_3445_);
                        crate::leanh::lean_dec_ref_known(v_x_3381_, 1);
                        v___f_3446_ = crate::leanh::lean_alloc_closure(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__3 as *mut core::ffi::c_void, 5, 3);
                        crate::leanh::lean_closure_set(v___f_3446_, 0, v_inst_3379_);
                        crate::leanh::lean_closure_set(v___f_3446_, 1, v_inst_3380_);
                        crate::leanh::lean_closure_set(v___f_3446_, 2, v___x_3383_);
                        v_sz_3447_ = lean_array_size(v_items_3445_);
                        v___x_3448_ = 0usize;
                        v___x_3085__overap_3449_ =
                            l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_3383_,
                                v___f_3446_,
                                v_sz_3447_,
                                v___x_3448_,
                                v_items_3445_,
                            );
                        v___x_3450_ =
                            crate::leanh::lean_apply_1(v___x_3085__overap_3449_, v_a_3382_);
                        v_fst_3451_ = crate::leanh::lean_ctor_get(v___x_3450_, 0);
                        v_snd_3452_ = crate::leanh::lean_ctor_get(v___x_3450_, 1);
                        v_isSharedCheck_3460_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3450_)) as u8;
                        if v_isSharedCheck_3460_ == 0 {
                            v___x_3454_ = v___x_3450_;
                            v_isShared_3455_ = v_isSharedCheck_3460_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3452_);
                            crate::leanh::lean_inc(v_fst_3451_);
                            crate::leanh::lean_dec(v___x_3450_);
                            v___x_3454_ = crate::leanh::lean_box(0);
                            v_isShared_3455_ = v_isSharedCheck_3460_;
                            state = 10;
                            continue;
                        }
                    }
                    5 => {
                        v_items_3461_ = crate::leanh::lean_ctor_get(v_x_3381_, 0);
                        crate::leanh::lean_inc_ref(v_items_3461_);
                        crate::leanh::lean_dec_ref_known(v_x_3381_, 1);
                        v___x_3462_ = crate::leanh::lean_alloc_closure(
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg
                                as *mut core::ffi::c_void,
                            4,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___x_3462_, 0, v_inst_3379_);
                        crate::leanh::lean_closure_set(v___x_3462_, 1, v_inst_3380_);
                        v_sz_3463_ = lean_array_size(v_items_3461_);
                        v___x_3464_ = 0usize;
                        v___x_3088__overap_3465_ =
                            l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_3383_,
                                v___x_3462_,
                                v_sz_3463_,
                                v___x_3464_,
                                v_items_3461_,
                            );
                        v___x_3466_ =
                            crate::leanh::lean_apply_1(v___x_3088__overap_3465_, v_a_3382_);
                        v_fst_3467_ = crate::leanh::lean_ctor_get(v___x_3466_, 0);
                        v_snd_3468_ = crate::leanh::lean_ctor_get(v___x_3466_, 1);
                        v_isSharedCheck_3478_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3466_)) as u8;
                        if v_isSharedCheck_3478_ == 0 {
                            v___x_3470_ = v___x_3466_;
                            v_isShared_3471_ = v_isSharedCheck_3478_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3468_);
                            crate::leanh::lean_inc(v_fst_3467_);
                            crate::leanh::lean_dec(v___x_3466_);
                            v___x_3470_ = crate::leanh::lean_box(0);
                            v_isShared_3471_ = v_isSharedCheck_3478_;
                            state = 12;
                            continue;
                        }
                    }
                    6 => {
                        v_content_3479_ = crate::leanh::lean_ctor_get(v_x_3381_, 0);
                        crate::leanh::lean_inc_ref(v_content_3479_);
                        crate::leanh::lean_dec_ref_known(v_x_3381_, 1);
                        v___x_3480_ = crate::leanh::lean_alloc_closure(
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg
                                as *mut core::ffi::c_void,
                            4,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___x_3480_, 0, v_inst_3379_);
                        crate::leanh::lean_closure_set(v___x_3480_, 1, v_inst_3380_);
                        v_sz_3481_ = lean_array_size(v_content_3479_);
                        v___x_3482_ = 0usize;
                        v___x_3091__overap_3483_ =
                            l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_3383_,
                                v___x_3480_,
                                v_sz_3481_,
                                v___x_3482_,
                                v_content_3479_,
                            );
                        v___x_3484_ =
                            crate::leanh::lean_apply_1(v___x_3091__overap_3483_, v_a_3382_);
                        v_fst_3485_ = crate::leanh::lean_ctor_get(v___x_3484_, 0);
                        v_snd_3486_ = crate::leanh::lean_ctor_get(v___x_3484_, 1);
                        v_isSharedCheck_3494_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3484_)) as u8;
                        if v_isSharedCheck_3494_ == 0 {
                            v___x_3488_ = v___x_3484_;
                            v_isShared_3489_ = v_isSharedCheck_3494_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3486_);
                            crate::leanh::lean_inc(v_fst_3485_);
                            crate::leanh::lean_dec(v___x_3484_);
                            v___x_3488_ = crate::leanh::lean_box(0);
                            v_isShared_3489_ = v_isSharedCheck_3494_;
                            state = 14;
                            continue;
                        }
                    }
                    _ => {
                        v_container_3495_ = crate::leanh::lean_ctor_get(v_x_3381_, 0);
                        crate::leanh::lean_inc(v_container_3495_);
                        v_content_3496_ = crate::leanh::lean_ctor_get(v_x_3381_, 1);
                        crate::leanh::lean_inc_ref(v_content_3496_);
                        crate::leanh::lean_dec_ref_known(v_x_3381_, 2);
                        v___x_3497_ =
                            l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0;
                        crate::leanh::lean_inc_ref(v_inst_3379_);
                        v___x_3498_ = crate::leanh::lean_alloc_closure(
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown
                                as *mut core::ffi::c_void,
                            5,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___x_3498_, 0, crate::leanh::lean_box(0));
                        crate::leanh::lean_closure_set(v___x_3498_, 1, v_inst_3379_);
                        crate::leanh::lean_closure_set(v___x_3498_, 2, v___x_3497_);
                        crate::leanh::lean_inc_ref(v_inst_3380_);
                        v___x_3499_ = crate::leanh::lean_alloc_closure(
                            l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg
                                as *mut core::ffi::c_void,
                            4,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___x_3499_, 0, v_inst_3379_);
                        crate::leanh::lean_closure_set(v___x_3499_, 1, v_inst_3380_);
                        v___x_3500_ = crate::leanh::lean_apply_5(
                            v_inst_3380_,
                            v___x_3498_,
                            v___x_3499_,
                            v_container_3495_,
                            v_content_3496_,
                            v_a_3382_,
                        );
                        return v___x_3500_;
                    }
                }
            }
            1 => {
                v___x_3388_ = l_Lean_Doc_MarkdownM_instInhabitedInlineCtx_default___closed__0;
                if v_isShared_3387_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3386_, 9);
                    v___x_3390_ = v___x_3386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3392_ = crate::leanh::lean_alloc_ctor(9, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_contents_3384_);
                    v___x_3390_ = v_reuseFailAlloc_3392_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3391_ =
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg(
                        v_inst_3379_,
                        v___x_3388_,
                        v___x_3390_,
                        v_a_3382_,
                    );
                return v___x_3391_;
            }
            3 => {
                v___x_3408_ = l_Lean_Doc_joinBlocks(v_fst_3403_);
                crate::leanh::lean_dec(v_fst_3403_);
                if v_isShared_3407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3406_, 0, v___x_3408_);
                    v___x_3410_ = v___x_3406_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3411_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_snd_3404_);
                    v___x_3410_ = v_reuseFailAlloc_3411_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3410_;
            }
            5 => {
                v_out_3418_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__22;
                v___x_3419_ = crate::leanh::lean_unsigned_to_nat(1);
                v___f_3420_ = crate::leanh::lean_alloc_closure(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__2___boxed as *mut core::ffi::c_void, 8, 4);
                crate::leanh::lean_closure_set(v___f_3420_, 0, v_inst_3379_);
                crate::leanh::lean_closure_set(v___f_3420_, 1, v_inst_3380_);
                crate::leanh::lean_closure_set(v___f_3420_, 2, v___x_3383_);
                crate::leanh::lean_closure_set(v___f_3420_, 3, v___x_3419_);
                v___x_3442_ = l_Int_toNat(v_start_3413_);
                crate::leanh::lean_dec(v_start_3413_);
                v___x_3443_ = lean_nat_dec_le(v___x_3419_, v___x_3442_);
                if v___x_3443_ == 0 {
                    crate::leanh::lean_dec(v___x_3442_);
                    v___y_3422_ = v___x_3419_;
                    state = 6;
                    continue;
                } else {
                    v___y_3422_ = v___x_3442_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3417_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3416_, 0);
                    crate::leanh::lean_ctor_set(v___x_3416_, 1, v___y_3422_);
                    crate::leanh::lean_ctor_set(v___x_3416_, 0, v_out_3418_);
                    v___x_3424_ = v___x_3416_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_out_3418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 1, v___y_3422_);
                    v___x_3424_ = v_reuseFailAlloc_3441_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_sz_3425_ = lean_array_size(v_items_3414_);
                v___x_3426_ = 0usize;
                v___x_2973__overap_3427_ =
                    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3383_,
                        v_items_3414_,
                        v___f_3420_,
                        v_sz_3425_,
                        v___x_3426_,
                        v___x_3424_,
                    );
                v___x_3428_ = crate::leanh::lean_apply_1(v___x_2973__overap_3427_, v_a_3382_);
                v_fst_3429_ = crate::leanh::lean_ctor_get(v___x_3428_, 0);
                crate::leanh::lean_inc(v_fst_3429_);
                v_snd_3430_ = crate::leanh::lean_ctor_get(v___x_3428_, 1);
                crate::leanh::lean_inc(v_snd_3430_);
                crate::leanh::lean_dec_ref(v___x_3428_);
                v_fst_3431_ = crate::leanh::lean_ctor_get(v_fst_3429_, 0);
                v_isSharedCheck_3439_ = (!crate::leanh::lean_is_exclusive(v_fst_3429_)) as u8;
                if v_isSharedCheck_3439_ == 0 {
                    v_unused_3440_ = crate::leanh::lean_ctor_get(v_fst_3429_, 1);
                    crate::leanh::lean_dec(v_unused_3440_);
                    v___x_3433_ = v_fst_3429_;
                    v_isShared_3434_ = v_isSharedCheck_3439_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3431_);
                    crate::leanh::lean_dec(v_fst_3429_);
                    v___x_3433_ = crate::leanh::lean_box(0);
                    v_isShared_3434_ = v_isSharedCheck_3439_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3435_ = l_Lean_Doc_joinBlocks(v_fst_3431_);
                crate::leanh::lean_dec(v_fst_3431_);
                if v_isShared_3434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3433_, 1, v_snd_3430_);
                    crate::leanh::lean_ctor_set(v___x_3433_, 0, v___x_3435_);
                    v___x_3437_ = v___x_3433_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3438_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_snd_3430_);
                    v___x_3437_ = v_reuseFailAlloc_3438_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3437_;
            }
            10 => {
                v___x_3456_ = l_Lean_Doc_joinBlocks(v_fst_3451_);
                crate::leanh::lean_dec(v_fst_3451_);
                if v_isShared_3455_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3454_, 0, v___x_3456_);
                    v___x_3458_ = v___x_3454_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3459_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_snd_3452_);
                    v___x_3458_ = v_reuseFailAlloc_3459_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3458_;
            }
            12 => {
                v___x_3472_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___closed__0;
                v___x_3473_ = l_Lean_Doc_joinBlocks(v_fst_3467_);
                crate::leanh::lean_dec(v_fst_3467_);
                v___x_3474_ = l_Lean_Doc_prefixLines(v___x_3472_, v___x_3473_);
                if v_isShared_3471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3470_, 0, v___x_3474_);
                    v___x_3476_ = v___x_3470_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_snd_3468_);
                    v___x_3476_ = v_reuseFailAlloc_3477_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3476_;
            }
            14 => {
                v___x_3490_ = l_Lean_Doc_joinBlocks(v_fst_3485_);
                crate::leanh::lean_dec(v_fst_3485_);
                if v_isShared_3489_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3488_, 0, v___x_3490_);
                    v___x_3492_ = v___x_3488_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3493_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_snd_3486_);
                    v___x_3492_ = v_reuseFailAlloc_3493_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0(
    mut v_inst_3501_: *mut crate::leanh::LeanObject,
    mut v_inst_3502_: *mut crate::leanh::LeanObject,
    mut v___x_3503_: *mut crate::leanh::LeanObject,
    mut v_item_3504_: *mut crate::leanh::LeanObject,
    mut v___y_3505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3507_: usize = 0;
    let mut v___x_3508_: usize = 0;
    let mut v___x_3123__overap_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3506_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3506_, 0, v_inst_3501_);
                crate::leanh::lean_closure_set(v___x_3506_, 1, v_inst_3502_);
                v_sz_3507_ = lean_array_size(v_item_3504_);
                v___x_3508_ = 0usize;
                v___x_3123__overap_3509_ =
                    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3503_,
                        v___x_3506_,
                        v_sz_3507_,
                        v___x_3508_,
                        v_item_3504_,
                    );
                v___x_3510_ = crate::leanh::lean_apply_1(v___x_3123__overap_3509_, v___y_3505_);
                v_fst_3511_ = crate::leanh::lean_ctor_get(v___x_3510_, 0);
                v_snd_3512_ = crate::leanh::lean_ctor_get(v___x_3510_, 1);
                v_isSharedCheck_3523_ = (!crate::leanh::lean_is_exclusive(v___x_3510_)) as u8;
                if v_isSharedCheck_3523_ == 0 {
                    v___x_3514_ = v___x_3510_;
                    v_isShared_3515_ = v_isSharedCheck_3523_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3512_);
                    crate::leanh::lean_inc(v_fst_3511_);
                    crate::leanh::lean_dec(v___x_3510_);
                    v___x_3514_ = crate::leanh::lean_box(0);
                    v_isShared_3515_ = v_isSharedCheck_3523_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3516_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__0;
                v___x_3517_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__0___closed__1;
                v___x_3518_ = l_Lean_Doc_joinBlocks(v_fst_3511_);
                crate::leanh::lean_dec(v_fst_3511_);
                v___x_3519_ = l_Lean_Doc_prefixListLines(v___x_3516_, v___x_3517_, v___x_3518_);
                crate::leanh::lean_dec_ref(v___x_3518_);
                if v_isShared_3515_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3514_, 0, v___x_3519_);
                    v___x_3521_ = v___x_3514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3522_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_snd_3512_);
                    v___x_3521_ = v_reuseFailAlloc_3522_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown(
    mut v_i_3524_: *mut crate::leanh::LeanObject,
    mut v_b_3525_: *mut crate::leanh::LeanObject,
    mut v_inst_3526_: *mut crate::leanh::LeanObject,
    mut v_inst_3527_: *mut crate::leanh::LeanObject,
    mut v_x_3528_: *mut crate::leanh::LeanObject,
    mut v_a_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3530_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(
        v_inst_3526_,
        v_inst_3527_,
        v_x_3528_,
        v_a_3529_,
    );
    return v___x_3530_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1___redArg(
    mut v_inst_3531_: *mut crate::leanh::LeanObject,
    mut v_inst_3532_: *mut crate::leanh::LeanObject,
    mut v_a_3533_: *mut crate::leanh::LeanObject,
    mut v_a_3534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3535_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(
        v_inst_3531_,
        v_inst_3532_,
        v_a_3533_,
        v_a_3534_,
    );
    return v___x_3535_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(
    mut v_i_3536_: *mut crate::leanh::LeanObject,
    mut v_b_3537_: *mut crate::leanh::LeanObject,
    mut v_inst_3538_: *mut crate::leanh::LeanObject,
    mut v_inst_3539_: *mut crate::leanh::LeanObject,
    mut v_a_3540_: *mut crate::leanh::LeanObject,
    mut v_a_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3542_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg(
        v_inst_3538_,
        v_inst_3539_,
        v_a_3540_,
        v_a_3541_,
    );
    return v___x_3542_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___redArg(
    mut v_inst_3543_: *mut crate::leanh::LeanObject,
    mut v_inst_3544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3545_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1
            as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3545_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3545_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3545_, 2, v_inst_3543_);
    crate::leanh::lean_closure_set(v___x_3545_, 3, v_inst_3544_);
    return v___x_3545_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock(
    mut v_i_3546_: *mut crate::leanh::LeanObject,
    mut v_b_3547_: *mut crate::leanh::LeanObject,
    mut v_inst_3548_: *mut crate::leanh::LeanObject,
    mut v_inst_3549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3550_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1
            as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3550_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3550_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3550_, 2, v_inst_3548_);
    crate::leanh::lean_closure_set(v___x_3550_, 3, v_inst_3549_);
    return v___x_3550_;
}
pub unsafe fn _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3551_: u32 = 0;
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3551_ = 35;
    v___x_3552_ = crate::leanh::lean_box_uint32(v___x_3551_);
    return v___x_3552_;
}
pub unsafe fn _init_l_Lean_Doc_partMarkdown___redArg___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3553_ = l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1;
    v___f_3554_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3554_, 0, v___x_3553_);
    return v___f_3554_;
}
pub unsafe fn l_Lean_Doc_partMarkdown___redArg___boxed(
    mut v_inst_3555_: *mut crate::leanh::LeanObject,
    mut v_inst_3556_: *mut crate::leanh::LeanObject,
    mut v_level_3557_: *mut crate::leanh::LeanObject,
    mut v_part_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3560_ = l_Lean_Doc_partMarkdown___redArg(
        v_inst_3555_,
        v_inst_3556_,
        v_level_3557_,
        v_part_3558_,
        v_a_3559_,
    );
    crate::leanh::lean_dec(v_level_3557_);
    return v_res_3560_;
}
pub unsafe fn l_Lean_Doc_partMarkdown___redArg(
    mut v_inst_3561_: *mut crate::leanh::LeanObject,
    mut v_inst_3562_: *mut crate::leanh::LeanObject,
    mut v_level_3563_: *mut crate::leanh::LeanObject,
    mut v_part_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_title_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_content_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subParts_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3571_: usize = 0;
    let mut v___x_3572_: usize = 0;
    let mut v___x_613__overap_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3578_: usize = 0;
    let mut v___x_616__overap_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3589_: usize = 0;
    let mut v___x_619__overap_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3596_: u8 = 0;
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3566_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___redArg___closed__19;
                v_title_3567_ = crate::leanh::lean_ctor_get(v_part_3564_, 0);
                crate::leanh::lean_inc_ref(v_title_3567_);
                v_content_3568_ = crate::leanh::lean_ctor_get(v_part_3564_, 3);
                crate::leanh::lean_inc_ref(v_content_3568_);
                v_subParts_3569_ = crate::leanh::lean_ctor_get(v_part_3564_, 4);
                crate::leanh::lean_inc_ref(v_subParts_3569_);
                crate::leanh::lean_dec_ref(v_part_3564_);
                crate::leanh::lean_inc_ref_n(v_inst_3561_, 2);
                v___x_3570_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instToMarkdownInlineOfMarkdownInline___private__1
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3570_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3570_, 1, v_inst_3561_);
                v_sz_3571_ = lean_array_size(v_title_3567_);
                v___x_3572_ = 0usize;
                v___x_613__overap_3573_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3566_,
                    v___x_3570_,
                    v_sz_3571_,
                    v___x_3572_,
                    v_title_3567_,
                );
                v___x_3574_ = crate::leanh::lean_apply_1(v___x_613__overap_3573_, v_a_3565_);
                v_fst_3575_ = crate::leanh::lean_ctor_get(v___x_3574_, 0);
                crate::leanh::lean_inc(v_fst_3575_);
                v_snd_3576_ = crate::leanh::lean_ctor_get(v___x_3574_, 1);
                crate::leanh::lean_inc(v_snd_3576_);
                crate::leanh::lean_dec_ref(v___x_3574_);
                crate::leanh::lean_inc_ref(v_inst_3562_);
                v___x_3577_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1
                        as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3577_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3577_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3577_, 2, v_inst_3561_);
                crate::leanh::lean_closure_set(v___x_3577_, 3, v_inst_3562_);
                v_sz_3578_ = lean_array_size(v_content_3568_);
                v___x_616__overap_3579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3566_,
                    v___x_3577_,
                    v_sz_3578_,
                    v___x_3572_,
                    v_content_3568_,
                );
                v___x_3580_ = crate::leanh::lean_apply_1(v___x_616__overap_3579_, v_snd_3576_);
                v_fst_3581_ = crate::leanh::lean_ctor_get(v___x_3580_, 0);
                crate::leanh::lean_inc(v_fst_3581_);
                v_snd_3582_ = crate::leanh::lean_ctor_get(v___x_3580_, 1);
                crate::leanh::lean_inc(v_snd_3582_);
                crate::leanh::lean_dec_ref(v___x_3580_);
                v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_joinBlocks_spec__0___closed__0;
                v___f_3584_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Doc_partMarkdown___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Doc_partMarkdown___redArg___closed__0_once),
                    _init_l_Lean_Doc_partMarkdown___redArg___closed__0,
                );
                v___x_3585_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3586_ = lean_nat_add(v_level_3563_, v___x_3585_);
                crate::leanh::lean_inc(v___x_3586_);
                v___x_3587_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(
                    crate::leanh::lean_box(0),
                    v___f_3584_,
                    v___x_3586_,
                    v___x_3583_,
                );
                v___x_3588_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_partMarkdown___redArg___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_3588_, 0, v_inst_3561_);
                crate::leanh::lean_closure_set(v___x_3588_, 1, v_inst_3562_);
                crate::leanh::lean_closure_set(v___x_3588_, 2, v___x_3586_);
                v_sz_3589_ = lean_array_size(v_subParts_3569_);
                v___x_619__overap_3590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3566_,
                    v___x_3588_,
                    v_sz_3589_,
                    v___x_3572_,
                    v_subParts_3569_,
                );
                v___x_3591_ = crate::leanh::lean_apply_1(v___x_619__overap_3590_, v_snd_3582_);
                v_fst_3592_ = crate::leanh::lean_ctor_get(v___x_3591_, 0);
                v_snd_3593_ = crate::leanh::lean_ctor_get(v___x_3591_, 1);
                v_isSharedCheck_3611_ = (!crate::leanh::lean_is_exclusive(v___x_3591_)) as u8;
                if v_isSharedCheck_3611_ == 0 {
                    v___x_3595_ = v___x_3591_;
                    v_isShared_3596_ = v_isSharedCheck_3611_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3593_);
                    crate::leanh::lean_inc(v_fst_3592_);
                    crate::leanh::lean_dec(v___x_3591_);
                    v___x_3595_ = crate::leanh::lean_box(0);
                    v_isShared_3596_ = v_isSharedCheck_3611_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3597_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode___closed__0;
                v___x_3598_ = lean_string_append(v___x_3587_, v___x_3597_);
                v___x_3599_ = lean_mk_empty_array_with_capacity(v___x_3585_);
                crate::leanh::lean_inc_ref_n(v___x_3599_, 2);
                v___x_3600_ = lean_array_push(v___x_3599_, v___x_3598_);
                v___x_3601_ = lean_array_push(v___x_3599_, v___x_3600_);
                v___x_3602_ = l_Array_append___redArg(v___x_3601_, v_fst_3575_);
                crate::leanh::lean_dec(v_fst_3575_);
                v___x_3603_ = l_Lean_Doc_joinInlines(v___x_3602_);
                crate::leanh::lean_dec_ref(v___x_3602_);
                v___x_3604_ = lean_array_push(v___x_3599_, v___x_3603_);
                v___x_3605_ = l_Array_append___redArg(v___x_3604_, v_fst_3581_);
                crate::leanh::lean_dec(v_fst_3581_);
                v___x_3606_ = l_Array_append___redArg(v___x_3605_, v_fst_3592_);
                crate::leanh::lean_dec(v_fst_3592_);
                v___x_3607_ = l_Lean_Doc_joinBlocks(v___x_3606_);
                crate::leanh::lean_dec_ref(v___x_3606_);
                if v_isShared_3596_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3595_, 0, v___x_3607_);
                    v___x_3609_ = v___x_3595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3610_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_snd_3593_);
                    v___x_3609_ = v_reuseFailAlloc_3610_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Doc_partMarkdown(
    mut v_i_3612_: *mut crate::leanh::LeanObject,
    mut v_b_3613_: *mut crate::leanh::LeanObject,
    mut v_p_3614_: *mut crate::leanh::LeanObject,
    mut v_inst_3615_: *mut crate::leanh::LeanObject,
    mut v_inst_3616_: *mut crate::leanh::LeanObject,
    mut v_level_3617_: *mut crate::leanh::LeanObject,
    mut v_part_3618_: *mut crate::leanh::LeanObject,
    mut v_a_3619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3620_ = l_Lean_Doc_partMarkdown___redArg(
        v_inst_3615_,
        v_inst_3616_,
        v_level_3617_,
        v_part_3618_,
        v_a_3619_,
    );
    return v___x_3620_;
}
pub unsafe fn l_Lean_Doc_partMarkdown___boxed(
    mut v_i_3621_: *mut crate::leanh::LeanObject,
    mut v_b_3622_: *mut crate::leanh::LeanObject,
    mut v_p_3623_: *mut crate::leanh::LeanObject,
    mut v_inst_3624_: *mut crate::leanh::LeanObject,
    mut v_inst_3625_: *mut crate::leanh::LeanObject,
    mut v_level_3626_: *mut crate::leanh::LeanObject,
    mut v_part_3627_: *mut crate::leanh::LeanObject,
    mut v_a_3628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3629_ = l_Lean_Doc_partMarkdown(
        v_i_3621_,
        v_b_3622_,
        v_p_3623_,
        v_inst_3624_,
        v_inst_3625_,
        v_level_3626_,
        v_part_3627_,
        v_a_3628_,
    );
    crate::leanh::lean_dec(v_level_3626_);
    return v_res_3629_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0(
    mut v_inst_3630_: *mut crate::leanh::LeanObject,
    mut v_inst_3631_: *mut crate::leanh::LeanObject,
    mut v_part_3632_: *mut crate::leanh::LeanObject,
    mut v___y_3633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3634_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3635_ = l_Lean_Doc_partMarkdown___redArg(
        v_inst_3630_,
        v_inst_3631_,
        v___x_3634_,
        v_part_3632_,
        v___y_3633_,
    );
    return v___x_3635_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg(
    mut v_inst_3636_: *mut crate::leanh::LeanObject,
    mut v_inst_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3638_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3638_, 0, v_inst_3636_);
    crate::leanh::lean_closure_set(v___f_3638_, 1, v_inst_3637_);
    return v___f_3638_;
}
pub unsafe fn l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock(
    mut v_i_3639_: *mut crate::leanh::LeanObject,
    mut v_b_3640_: *mut crate::leanh::LeanObject,
    mut v_p_3641_: *mut crate::leanh::LeanObject,
    mut v_inst_3642_: *mut crate::leanh::LeanObject,
    mut v_inst_3643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3644_ = crate::leanh::lean_alloc_closure(
        l_Lean_Doc_instToMarkdownPartOfMarkdownInlineOfMarkdownBlock___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3644_, 0, v_inst_3642_);
    crate::leanh::lean_closure_set(v___f_3644_, 1, v_inst_3643_);
    return v___f_3644_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString_Markdown(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_DocString_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1 = _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1();
    crate::leanh::lean_mark_persistent(l___private_Lean_DocString_Markdown_0__Lean_Doc_midLineSpecial___closed__3___boxed__const__1);
    l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1 = _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(l___private_Lean_DocString_Markdown_0__Lean_Doc_markerPrefixSpecial___closed__0___boxed__const__1);
    l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1 =
        _init_l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l_Lean_Doc_partMarkdown___redArg___closed__0___boxed__const__1,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString_Markdown(
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
pub unsafe fn initialize_Lean_DocString_Markdown(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_DocString_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Markdown(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DocString_Markdown(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_DocString_Markdown(builtin);
}

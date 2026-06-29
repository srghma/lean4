// Lean compiler output
// Module: Lean.Compiler.Main
// Imports: Lean.Compiler.LCNF Lean.Compiler.Options
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_replaceRef};
use crate::r#gen::Lean::Compiler::LCNF::Main::l_Lean_Compiler_LCNF_main;
use crate::r#gen::Lean::Compiler::LCNF::{
    initialize_Lean_Compiler_LCNF, runtime_initialize_Lean_Compiler_LCNF,
};
use crate::r#gen::Lean::Compiler::Options::{
    initialize_Lean_Compiler_Options, l_Lean_Compiler_compiler_postponeCompile,
    runtime_initialize_Lean_Compiler_Options,
};
use crate::r#gen::Lean::CoreM::l_Lean_diagnostics;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::Profile::l_Lean_profileitIOUnsafe___redArg;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_registerTraceClass, l_Lean_trace_profiler, l_Lean_trace_profiler_threshold,
    l_Lean_trace_profiler_useHeartbeats,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Float::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_to_list, lean_mk_empty_array_with_capacity,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_compile___lam__0___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [99, 111, 109, 112, 105, 108, 105, 110, 103, 58, 32, 0],
    };
static mut l_Lean_Compiler_compile___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_compile___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_compile___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_compile___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5: f64 = 0.0;
static mut l_Lean_Compiler_compile___lam__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_compile___lam__1___closed__0: f64 = 0.0;
static mut l_Lean_Compiler_compile___lam__1___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_compile___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_compile___lam__1___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_compile___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_compile___lam__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_compile___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_compile___closed__0_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [99, 111, 109, 112, 105, 108, 101, 114, 32, 110, 101, 119, 0],
    };
static mut l_Lean_Compiler_compile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_compile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_compile___closed__1_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0],
    };
static mut l_Lean_Compiler_compile___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_compile___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_compile___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_compile___closed__1_value)
                as *mut crate::leanh::LeanObject,
            2042452093243897853 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_compile___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_compile___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_compile___closed__3_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Compiler_compile___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_compile___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_compile___closed__1_value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 97, 105, 110, 0]};
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15545510689747167085 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,928043634643136088 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4514859094366734289 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_compile___closed__1_value) as *mut crate::leanh::LeanObject,14955299278496587999 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5458129425496714750 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12461663696602845983 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4503797046311743186 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_compile___closed__1_value) as *mut crate::leanh::LeanObject,11974195153158276896 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13055568396239690981 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 509999922 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10816224647275005754 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12701501349079814421 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17263458831302729429 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,13735003437155114584 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 97, 116, 0]};
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_compile___closed__1_value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4054921005328035601 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(
    mut v_opts_761_: *mut crate::leanh::LeanObject,
    mut v_opt_762_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_763_ = crate::leanh::lean_ctor_get(v_opt_762_, 0);
    v_defValue_764_ = crate::leanh::lean_ctor_get(v_opt_762_, 1);
    v_map_765_ = crate::leanh::lean_ctor_get(v_opts_761_, 0);
    v___x_766_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_765_,
            v_name_763_,
        );
    if crate::leanh::lean_obj_tag(v___x_766_) == 0 {
        let mut v___x_767_: u8 = 0;
        v___x_767_ = (crate::leanh::lean_unbox(v_defValue_764_) as u8);
        return v___x_767_;
    } else {
        let mut v_val_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_768_ = crate::leanh::lean_ctor_get(v___x_766_, 0);
        crate::leanh::lean_inc(v_val_768_);
        crate::leanh::lean_dec_ref_known(v___x_766_, 1);
        if crate::leanh::lean_obj_tag(v_val_768_) == 1 {
            let mut v_v_769_: u8 = 0;
            v_v_769_ = crate::leanh::lean_ctor_get_uint8(v_val_768_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_768_, 0);
            return v_v_769_;
        } else {
            let mut v___x_770_: u8 = 0;
            crate::leanh::lean_dec(v_val_768_);
            v___x_770_ = (crate::leanh::lean_unbox(v_defValue_764_) as u8);
            return v___x_770_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2___boxed(
    mut v_opts_771_: *mut crate::leanh::LeanObject,
    mut v_opt_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_773_: u8 = 0;
    let mut v_r_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(v_opts_771_, v_opt_772_);
    crate::leanh::lean_dec_ref(v_opt_772_);
    crate::leanh::lean_dec_ref(v_opts_771_);
    v_r_774_ = crate::leanh::lean_box((v_res_773_) as usize);
    return v_r_774_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(
    mut v_opts_775_: *mut crate::leanh::LeanObject,
    mut v_opt_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_777_ = crate::leanh::lean_ctor_get(v_opt_776_, 0);
    v_defValue_778_ = crate::leanh::lean_ctor_get(v_opt_776_, 1);
    v_map_779_ = crate::leanh::lean_ctor_get(v_opts_775_, 0);
    v___x_780_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_779_,
            v_name_777_,
        );
    if crate::leanh::lean_obj_tag(v___x_780_) == 0 {
        crate::leanh::lean_inc(v_defValue_778_);
        return v_defValue_778_;
    } else {
        let mut v_val_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_781_ = crate::leanh::lean_ctor_get(v___x_780_, 0);
        crate::leanh::lean_inc(v_val_781_);
        crate::leanh::lean_dec_ref_known(v___x_780_, 1);
        if crate::leanh::lean_obj_tag(v_val_781_) == 3 {
            let mut v_v_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_782_ = crate::leanh::lean_ctor_get(v_val_781_, 0);
            crate::leanh::lean_inc(v_v_782_);
            crate::leanh::lean_dec_ref_known(v_val_781_, 1);
            return v_v_782_;
        } else {
            crate::leanh::lean_dec(v_val_781_);
            crate::leanh::lean_inc(v_defValue_778_);
            return v_defValue_778_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3___boxed(
    mut v_opts_783_: *mut crate::leanh::LeanObject,
    mut v_opt_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_785_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(v_opts_783_, v_opt_784_);
    crate::leanh::lean_dec_ref(v_opt_784_);
    crate::leanh::lean_dec_ref(v_opts_783_);
    return v_res_785_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_786_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_787_ = lean_mk_empty_array_with_capacity(v___x_786_);
    v___x_788_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_788_, 0, v___x_787_);
    return v___x_788_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_789_: usize = 0;
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_789_ = 5usize;
    v___x_790_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_791_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_792_ = lean_mk_empty_array_with_capacity(v___x_791_);
    v___x_793_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__0);
    v___x_794_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_794_, 0, v___x_793_);
    crate::leanh::lean_ctor_set(v___x_794_, 1, v___x_792_);
    crate::leanh::lean_ctor_set(v___x_794_, 2, v___x_790_);
    crate::leanh::lean_ctor_set(v___x_794_, 3, v___x_790_);
    crate::leanh::lean_ctor_set_usize(v___x_794_, 4, v___x_789_);
    return v___x_794_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(
    mut v___y_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_812_: u8 = 0;
    let mut v_tid_813_: u64 = 0;
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_816_: u8 = 0;
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_826_: u8 = 0;
    let mut v_unused_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_797_ = lean_st_ref_get(v___y_795_);
                v_traceState_798_ = crate::leanh::lean_ctor_get(v___x_797_, 4);
                crate::leanh::lean_inc_ref(v_traceState_798_);
                crate::leanh::lean_dec(v___x_797_);
                v_traces_799_ = crate::leanh::lean_ctor_get(v_traceState_798_, 0);
                crate::leanh::lean_inc_ref(v_traces_799_);
                crate::leanh::lean_dec_ref(v_traceState_798_);
                v___x_800_ = lean_st_ref_take(v___y_795_);
                v_traceState_801_ = crate::leanh::lean_ctor_get(v___x_800_, 4);
                v_env_802_ = crate::leanh::lean_ctor_get(v___x_800_, 0);
                v_nextMacroScope_803_ = crate::leanh::lean_ctor_get(v___x_800_, 1);
                v_ngen_804_ = crate::leanh::lean_ctor_get(v___x_800_, 2);
                v_auxDeclNGen_805_ = crate::leanh::lean_ctor_get(v___x_800_, 3);
                v_cache_806_ = crate::leanh::lean_ctor_get(v___x_800_, 5);
                v_messages_807_ = crate::leanh::lean_ctor_get(v___x_800_, 6);
                v_infoState_808_ = crate::leanh::lean_ctor_get(v___x_800_, 7);
                v_snapshotTasks_809_ = crate::leanh::lean_ctor_get(v___x_800_, 8);
                v_isSharedCheck_828_ = (!crate::leanh::lean_is_exclusive(v___x_800_)) as u8;
                if v_isSharedCheck_828_ == 0 {
                    v___x_811_ = v___x_800_;
                    v_isShared_812_ = v_isSharedCheck_828_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_809_);
                    crate::leanh::lean_inc(v_infoState_808_);
                    crate::leanh::lean_inc(v_messages_807_);
                    crate::leanh::lean_inc(v_cache_806_);
                    crate::leanh::lean_inc(v_traceState_801_);
                    crate::leanh::lean_inc(v_auxDeclNGen_805_);
                    crate::leanh::lean_inc(v_ngen_804_);
                    crate::leanh::lean_inc(v_nextMacroScope_803_);
                    crate::leanh::lean_inc(v_env_802_);
                    crate::leanh::lean_dec(v___x_800_);
                    v___x_811_ = crate::leanh::lean_box(0);
                    v_isShared_812_ = v_isSharedCheck_828_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_813_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_801_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_826_ = (!crate::leanh::lean_is_exclusive(v_traceState_801_)) as u8;
                if v_isSharedCheck_826_ == 0 {
                    v_unused_827_ = crate::leanh::lean_ctor_get(v_traceState_801_, 0);
                    crate::leanh::lean_dec(v_unused_827_);
                    v___x_815_ = v_traceState_801_;
                    v_isShared_816_ = v_isSharedCheck_826_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_801_);
                    v___x_815_ = crate::leanh::lean_box(0);
                    v_isShared_816_ = v_isSharedCheck_826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_817_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___closed__1);
                if v_isShared_816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_815_, 0, v___x_817_);
                    v___x_819_ = v___x_815_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_825_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_817_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_825_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_813_,
                    );
                    v___x_819_ = v_reuseFailAlloc_825_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_812_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_811_, 4, v___x_819_);
                    v___x_821_ = v___x_811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_824_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 0, v_env_802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 1, v_nextMacroScope_803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 2, v_ngen_804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 3, v_auxDeclNGen_805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 4, v___x_819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 5, v_cache_806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 6, v_messages_807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 7, v_infoState_808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 8, v_snapshotTasks_809_);
                    v___x_821_ = v_reuseFailAlloc_824_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_822_ = lean_st_ref_set(v___y_795_, v___x_821_);
                v___x_823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_823_, 0, v_traces_799_);
                return v___x_823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg___boxed(
    mut v___y_829_: *mut crate::leanh::LeanObject,
    mut v___y_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_831_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_829_);
    crate::leanh::lean_dec(v___y_829_);
    return v_res_831_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4(
    mut v___y_832_: *mut crate::leanh::LeanObject,
    mut v___y_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_833_);
    return v___x_835_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___boxed(
    mut v___y_836_: *mut crate::leanh::LeanObject,
    mut v___y_837_: *mut crate::leanh::LeanObject,
    mut v___y_838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_839_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4(
            v___y_836_, v___y_837_,
        );
    crate::leanh::lean_dec(v___y_837_);
    crate::leanh::lean_dec_ref(v___y_836_);
    return v_res_839_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(
    mut v_category_840_: *mut crate::leanh::LeanObject,
    mut v_opts_841_: *mut crate::leanh::LeanObject,
    mut v_act_842_: *mut crate::leanh::LeanObject,
    mut v_decl_843_: *mut crate::leanh::LeanObject,
    mut v___y_844_: *mut crate::leanh::LeanObject,
    mut v___y_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_845_);
    crate::leanh::lean_inc_ref(v___y_844_);
    v___x_847_ = crate::leanh::lean_apply_2(v_act_842_, v___y_844_, v___y_845_);
    v___x_848_ =
        l_Lean_profileitIOUnsafe___redArg(v_category_840_, v_opts_841_, v___x_847_, v_decl_843_);
    return v___x_848_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg___boxed(
    mut v_category_849_: *mut crate::leanh::LeanObject,
    mut v_opts_850_: *mut crate::leanh::LeanObject,
    mut v_act_851_: *mut crate::leanh::LeanObject,
    mut v_decl_852_: *mut crate::leanh::LeanObject,
    mut v___y_853_: *mut crate::leanh::LeanObject,
    mut v___y_854_: *mut crate::leanh::LeanObject,
    mut v___y_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_856_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(
        v_category_849_,
        v_opts_850_,
        v_act_851_,
        v_decl_852_,
        v___y_853_,
        v___y_854_,
    );
    crate::leanh::lean_dec(v___y_854_);
    crate::leanh::lean_dec_ref(v___y_853_);
    crate::leanh::lean_dec_ref(v_opts_850_);
    crate::leanh::lean_dec_ref(v_category_849_);
    return v_res_856_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(
    mut v_00_u03b1_857_: *mut crate::leanh::LeanObject,
    mut v_category_858_: *mut crate::leanh::LeanObject,
    mut v_opts_859_: *mut crate::leanh::LeanObject,
    mut v_act_860_: *mut crate::leanh::LeanObject,
    mut v_decl_861_: *mut crate::leanh::LeanObject,
    mut v___y_862_: *mut crate::leanh::LeanObject,
    mut v___y_863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(
        v_category_858_,
        v_opts_859_,
        v_act_860_,
        v_decl_861_,
        v___y_862_,
        v___y_863_,
    );
    return v___x_865_;
}
pub unsafe fn l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___boxed(
    mut v_00_u03b1_866_: *mut crate::leanh::LeanObject,
    mut v_category_867_: *mut crate::leanh::LeanObject,
    mut v_opts_868_: *mut crate::leanh::LeanObject,
    mut v_act_869_: *mut crate::leanh::LeanObject,
    mut v_decl_870_: *mut crate::leanh::LeanObject,
    mut v___y_871_: *mut crate::leanh::LeanObject,
    mut v___y_872_: *mut crate::leanh::LeanObject,
    mut v___y_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_874_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6(
        v_00_u03b1_866_,
        v_category_867_,
        v_opts_868_,
        v_act_869_,
        v_decl_870_,
        v___y_871_,
        v___y_872_,
    );
    crate::leanh::lean_dec(v___y_872_);
    crate::leanh::lean_dec_ref(v___y_871_);
    crate::leanh::lean_dec_ref(v_opts_868_);
    crate::leanh::lean_dec_ref(v_category_867_);
    return v_res_874_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(
    mut v_a_875_: *mut crate::leanh::LeanObject,
    mut v_a_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_882_: u8 = 0;
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_875_) == 0 {
                    v___x_877_ = l_List_reverse___redArg(v_a_876_);
                    return v___x_877_;
                } else {
                    v_head_878_ = crate::leanh::lean_ctor_get(v_a_875_, 0);
                    v_tail_879_ = crate::leanh::lean_ctor_get(v_a_875_, 1);
                    v_isSharedCheck_888_ = (!crate::leanh::lean_is_exclusive(v_a_875_)) as u8;
                    if v_isSharedCheck_888_ == 0 {
                        v___x_881_ = v_a_875_;
                        v_isShared_882_ = v_isSharedCheck_888_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_879_);
                        crate::leanh::lean_inc(v_head_878_);
                        crate::leanh::lean_dec(v_a_875_);
                        v___x_881_ = crate::leanh::lean_box(0);
                        v_isShared_882_ = v_isSharedCheck_888_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_883_ = l_Lean_MessageData_ofName(v_head_878_);
                if v_isShared_882_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_881_, 1, v_a_876_);
                    crate::leanh::lean_ctor_set(v___x_881_, 0, v___x_883_);
                    v___x_885_ = v___x_881_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_887_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_887_, 1, v_a_876_);
                    v___x_885_ = v_reuseFailAlloc_887_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_875_ = v_tail_879_;
                v_a_876_ = v___x_885_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_compile___lam__0___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = l_Lean_Compiler_compile___lam__0___closed__0;
    v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
    return v___x_891_;
}
pub unsafe fn l_Lean_Compiler_compile___lam__0(
    mut v_declNames_892_: *mut crate::leanh::LeanObject,
    mut v_x_893_: *mut crate::leanh::LeanObject,
    mut v___y_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_897_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__0___closed__1_once),
        _init_l_Lean_Compiler_compile___lam__0___closed__1,
    );
    v___x_898_ = lean_array_to_list(v_declNames_892_);
    v___x_899_ = crate::leanh::lean_box(0);
    v___x_900_ = l_List_mapTR_loop___at___00Lean_Compiler_compile_spec__0(v___x_898_, v___x_899_);
    v___x_901_ = l_Lean_MessageData_ofList(v___x_900_);
    v___x_902_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_902_, 0, v___x_897_);
    crate::leanh::lean_ctor_set(v___x_902_, 1, v___x_901_);
    v___x_903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_903_, 0, v___x_902_);
    return v___x_903_;
}
pub unsafe fn l_Lean_Compiler_compile___lam__0___boxed(
    mut v_declNames_904_: *mut crate::leanh::LeanObject,
    mut v_x_905_: *mut crate::leanh::LeanObject,
    mut v___y_906_: *mut crate::leanh::LeanObject,
    mut v___y_907_: *mut crate::leanh::LeanObject,
    mut v___y_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_909_ =
        l_Lean_Compiler_compile___lam__0(v_declNames_904_, v_x_905_, v___y_906_, v___y_907_);
    crate::leanh::lean_dec(v___y_907_);
    crate::leanh::lean_dec_ref(v___y_906_);
    crate::leanh::lean_dec_ref(v_x_905_);
    return v_res_909_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(
    mut v_o_913_: *mut crate::leanh::LeanObject,
    mut v_k_914_: *mut crate::leanh::LeanObject,
    mut v_v_915_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_917_: u8 = 0;
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_920_: u8 = 0;
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_916_ = crate::leanh::lean_ctor_get(v_o_913_, 0);
                v_hasTrace_917_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_913_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_931_ = (!crate::leanh::lean_is_exclusive(v_o_913_)) as u8;
                if v_isSharedCheck_931_ == 0 {
                    v___x_919_ = v_o_913_;
                    v_isShared_920_ = v_isSharedCheck_931_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_916_);
                    crate::leanh::lean_dec(v_o_913_);
                    v___x_919_ = crate::leanh::lean_box(0);
                    v_isShared_920_ = v_isSharedCheck_931_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_921_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_921_, 0 as u32, v_v_915_);
                crate::leanh::lean_inc(v_k_914_);
                v___x_922_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_914_, v___x_921_, v_map_916_);
                if v_hasTrace_917_ == 0 {
                    v___x_923_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1;
                    v___x_924_ = l_Lean_Name_isPrefixOf(v___x_923_, v_k_914_);
                    crate::leanh::lean_dec(v_k_914_);
                    if v_isShared_920_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_922_);
                        v___x_926_ = v___x_919_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_927_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_922_);
                        v___x_926_ = v_reuseFailAlloc_927_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_914_);
                    if v_isShared_920_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_922_);
                        v___x_929_ = v___x_919_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_930_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_922_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_930_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_917_,
                        );
                        v___x_929_ = v_reuseFailAlloc_930_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_926_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_924_,
                );
                return v___x_926_;
            }
            3 => {
                return v___x_929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___boxed(
    mut v_o_932_: *mut crate::leanh::LeanObject,
    mut v_k_933_: *mut crate::leanh::LeanObject,
    mut v_v_934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_935_: u8 = 0;
    let mut v_res_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_935_ = (crate::leanh::lean_unbox(v_v_934_) as u8);
    v_res_936_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(
            v_o_932_,
            v_k_933_,
            v_v_boxed_935_,
        );
    return v_res_936_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(
    mut v_opts_937_: *mut crate::leanh::LeanObject,
    mut v_opt_938_: *mut crate::leanh::LeanObject,
    mut v_val_939_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_940_ = crate::leanh::lean_ctor_get(v_opt_938_, 0);
    crate::leanh::lean_inc(v_name_940_);
    crate::leanh::lean_dec_ref(v_opt_938_);
    v___x_941_ =
        l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1(
            v_opts_937_,
            v_name_940_,
            v_val_939_,
        );
    return v___x_941_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1___boxed(
    mut v_opts_942_: *mut crate::leanh::LeanObject,
    mut v_opt_943_: *mut crate::leanh::LeanObject,
    mut v_val_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_945_: u8 = 0;
    let mut v_res_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_945_ = (crate::leanh::lean_unbox(v_val_944_) as u8);
    v_res_946_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(
        v_opts_942_,
        v_opt_943_,
        v_val_boxed_945_,
    );
    return v_res_946_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(
    mut v_x_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_952_: u8 = 0;
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_956_: u8 = 0;
    let mut v_a_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_960_: u8 = 0;
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_947_) == 0 {
                    v_a_949_ = crate::leanh::lean_ctor_get(v_x_947_, 0);
                    v_isSharedCheck_956_ = (!crate::leanh::lean_is_exclusive(v_x_947_)) as u8;
                    if v_isSharedCheck_956_ == 0 {
                        v___x_951_ = v_x_947_;
                        v_isShared_952_ = v_isSharedCheck_956_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_949_);
                        crate::leanh::lean_dec(v_x_947_);
                        v___x_951_ = crate::leanh::lean_box(0);
                        v_isShared_952_ = v_isSharedCheck_956_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_957_ = crate::leanh::lean_ctor_get(v_x_947_, 0);
                    v_isSharedCheck_964_ = (!crate::leanh::lean_is_exclusive(v_x_947_)) as u8;
                    if v_isSharedCheck_964_ == 0 {
                        v___x_959_ = v_x_947_;
                        v_isShared_960_ = v_isSharedCheck_964_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_957_);
                        crate::leanh::lean_dec(v_x_947_);
                        v___x_959_ = crate::leanh::lean_box(0);
                        v_isShared_960_ = v_isSharedCheck_964_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_952_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_951_, 1);
                    v___x_954_ = v___x_951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_955_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
                    v___x_954_ = v_reuseFailAlloc_955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_954_;
            }
            3 => {
                if v_isShared_960_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_959_, 0);
                    v___x_962_ = v___x_959_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_963_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
                    v___x_962_ = v_reuseFailAlloc_963_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg___boxed(
    mut v_x_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_967_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_x_965_);
    return v_res_967_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(
    mut v_sz_968_: usize,
    mut v_i_969_: usize,
    mut v_bs_970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_971_: u8 = 0;
    let mut v_v_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: usize = 0;
    let mut v___x_977_: usize = 0;
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_971_ = lean_usize_dec_lt(v_i_969_, v_sz_968_);
                if v___x_971_ == 0 {
                    return v_bs_970_;
                } else {
                    v_v_972_ = lean_array_uget_borrowed(v_bs_970_, v_i_969_);
                    v_msg_973_ = crate::leanh::lean_ctor_get(v_v_972_, 1);
                    crate::leanh::lean_inc_ref(v_msg_973_);
                    v___x_974_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_975_ = lean_array_uset(v_bs_970_, v_i_969_, v___x_974_);
                    v___x_976_ = 1usize;
                    v___x_977_ = lean_usize_add(v_i_969_, v___x_976_);
                    v___x_978_ = lean_array_uset(v_bs_x27_975_, v_i_969_, v_msg_973_);
                    v_i_969_ = v___x_977_;
                    v_bs_970_ = v___x_978_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9___boxed(
    mut v_sz_980_: *mut crate::leanh::LeanObject,
    mut v_i_981_: *mut crate::leanh::LeanObject,
    mut v_bs_982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_983_: usize = 0;
    let mut v_i_boxed_984_: usize = 0;
    let mut v_res_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_983_ = crate::leanh::lean_unbox_usize(v_sz_980_);
    crate::leanh::lean_dec(v_sz_980_);
    v_i_boxed_984_ = crate::leanh::lean_unbox_usize(v_i_981_);
    crate::leanh::lean_dec(v_i_981_);
    v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(v_sz_boxed_983_, v_i_boxed_984_, v_bs_982_);
    return v_res_985_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_986_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_986_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__0);
    v___x_988_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_988_, 0, v___x_987_);
    return v___x_988_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1);
    v___x_990_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_991_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_991_, 0, v___x_990_);
    crate::leanh::lean_ctor_set(v___x_991_, 1, v___x_990_);
    crate::leanh::lean_ctor_set(v___x_991_, 2, v___x_990_);
    crate::leanh::lean_ctor_set(v___x_991_, 3, v___x_990_);
    crate::leanh::lean_ctor_set(v___x_991_, 4, v___x_989_);
    crate::leanh::lean_ctor_set(v___x_991_, 5, v___x_989_);
    crate::leanh::lean_ctor_set(v___x_991_, 6, v___x_989_);
    crate::leanh::lean_ctor_set(v___x_991_, 7, v___x_989_);
    crate::leanh::lean_ctor_set(v___x_991_, 8, v___x_989_);
    crate::leanh::lean_ctor_set(v___x_991_, 9, v___x_989_);
    return v___x_991_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_993_ = lean_mk_empty_array_with_capacity(v___x_992_);
    v___x_994_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_994_, 0, v___x_993_);
    return v___x_994_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_995_: usize = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = 5usize;
    v___x_996_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_997_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_998_ = lean_mk_empty_array_with_capacity(v___x_997_);
    v___x_999_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__3);
    v___x_1000_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1000_, 0, v___x_999_);
    crate::leanh::lean_ctor_set(v___x_1000_, 1, v___x_998_);
    crate::leanh::lean_ctor_set(v___x_1000_, 2, v___x_996_);
    crate::leanh::lean_ctor_set(v___x_1000_, 3, v___x_996_);
    crate::leanh::lean_ctor_set_usize(v___x_1000_, 4, v___x_995_);
    return v___x_1000_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1001_ = crate::leanh::lean_box(1);
    v___x_1002_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__4);
    v___x_1003_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__1);
    v___x_1004_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1004_, 0, v___x_1003_);
    crate::leanh::lean_ctor_set(v___x_1004_, 1, v___x_1002_);
    crate::leanh::lean_ctor_set(v___x_1004_, 2, v___x_1001_);
    return v___x_1004_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(
    mut v_msgData_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1009_ = lean_st_ref_get(v___y_1007_);
    v_env_1010_ = crate::leanh::lean_ctor_get(v___x_1009_, 0);
    crate::leanh::lean_inc_ref(v_env_1010_);
    crate::leanh::lean_dec(v___x_1009_);
    v_options_1011_ = crate::leanh::lean_ctor_get(v___y_1006_, 2);
    v___x_1012_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__2);
    v___x_1013_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___closed__5);
    crate::leanh::lean_inc_ref(v_options_1011_);
    v___x_1014_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1014_, 0, v_env_1010_);
    crate::leanh::lean_ctor_set(v___x_1014_, 1, v___x_1012_);
    crate::leanh::lean_ctor_set(v___x_1014_, 2, v___x_1013_);
    crate::leanh::lean_ctor_set(v___x_1014_, 3, v_options_1011_);
    v___x_1015_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1015_, 0, v___x_1014_);
    crate::leanh::lean_ctor_set(v___x_1015_, 1, v_msgData_1005_);
    v___x_1016_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1016_, 0, v___x_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10___boxed(
    mut v_msgData_1017_: *mut crate::leanh::LeanObject,
    mut v___y_1018_: *mut crate::leanh::LeanObject,
    mut v___y_1019_: *mut crate::leanh::LeanObject,
    mut v___y_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1021_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(v_msgData_1017_, v___y_1018_, v___y_1019_);
    crate::leanh::lean_dec(v___y_1019_);
    crate::leanh::lean_dec_ref(v___y_1018_);
    return v_res_1021_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(
    mut v_oldTraces_1022_: *mut crate::leanh::LeanObject,
    mut v_data_1023_: *mut crate::leanh::LeanObject,
    mut v_ref_1024_: *mut crate::leanh::LeanObject,
    mut v_msg_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1041_: u8 = 0;
    let mut v_cancelTk_x3f_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1043_: u8 = 0;
    let mut v_inheritedTraceOptions_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1051_: usize = 0;
    let mut v___x_1052_: usize = 0;
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1059_: u8 = 0;
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1072_: u8 = 0;
    let mut v_tid_1073_: u64 = 0;
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1076_: u8 = 0;
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1090_: u8 = 0;
    let mut v_unused_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1092_: u8 = 0;
    let mut v_isSharedCheck_1093_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1029_ = crate::leanh::lean_ctor_get(v___y_1026_, 0);
                v_fileMap_1030_ = crate::leanh::lean_ctor_get(v___y_1026_, 1);
                v_options_1031_ = crate::leanh::lean_ctor_get(v___y_1026_, 2);
                v_currRecDepth_1032_ = crate::leanh::lean_ctor_get(v___y_1026_, 3);
                v_maxRecDepth_1033_ = crate::leanh::lean_ctor_get(v___y_1026_, 4);
                v_ref_1034_ = crate::leanh::lean_ctor_get(v___y_1026_, 5);
                v_currNamespace_1035_ = crate::leanh::lean_ctor_get(v___y_1026_, 6);
                v_openDecls_1036_ = crate::leanh::lean_ctor_get(v___y_1026_, 7);
                v_initHeartbeats_1037_ = crate::leanh::lean_ctor_get(v___y_1026_, 8);
                v_maxHeartbeats_1038_ = crate::leanh::lean_ctor_get(v___y_1026_, 9);
                v_quotContext_1039_ = crate::leanh::lean_ctor_get(v___y_1026_, 10);
                v_currMacroScope_1040_ = crate::leanh::lean_ctor_get(v___y_1026_, 11);
                v_diag_1041_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1026_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1042_ = crate::leanh::lean_ctor_get(v___y_1026_, 12);
                v_suppressElabErrors_1043_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1026_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1044_ = crate::leanh::lean_ctor_get(v___y_1026_, 13);
                v___x_1045_ = lean_st_ref_get(v___y_1027_);
                v_traceState_1046_ = crate::leanh::lean_ctor_get(v___x_1045_, 4);
                crate::leanh::lean_inc_ref(v_traceState_1046_);
                crate::leanh::lean_dec(v___x_1045_);
                v_traces_1047_ = crate::leanh::lean_ctor_get(v_traceState_1046_, 0);
                crate::leanh::lean_inc_ref(v_traces_1047_);
                crate::leanh::lean_dec_ref(v_traceState_1046_);
                v_ref_1048_ = l_Lean_replaceRef(v_ref_1024_, v_ref_1034_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1044_);
                crate::leanh::lean_inc(v_cancelTk_x3f_1042_);
                crate::leanh::lean_inc(v_currMacroScope_1040_);
                crate::leanh::lean_inc(v_quotContext_1039_);
                crate::leanh::lean_inc(v_maxHeartbeats_1038_);
                crate::leanh::lean_inc(v_initHeartbeats_1037_);
                crate::leanh::lean_inc(v_openDecls_1036_);
                crate::leanh::lean_inc(v_currNamespace_1035_);
                crate::leanh::lean_inc(v_maxRecDepth_1033_);
                crate::leanh::lean_inc(v_currRecDepth_1032_);
                crate::leanh::lean_inc_ref(v_options_1031_);
                crate::leanh::lean_inc_ref(v_fileMap_1030_);
                crate::leanh::lean_inc_ref(v_fileName_1029_);
                v___x_1049_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1049_, 0, v_fileName_1029_);
                crate::leanh::lean_ctor_set(v___x_1049_, 1, v_fileMap_1030_);
                crate::leanh::lean_ctor_set(v___x_1049_, 2, v_options_1031_);
                crate::leanh::lean_ctor_set(v___x_1049_, 3, v_currRecDepth_1032_);
                crate::leanh::lean_ctor_set(v___x_1049_, 4, v_maxRecDepth_1033_);
                crate::leanh::lean_ctor_set(v___x_1049_, 5, v_ref_1048_);
                crate::leanh::lean_ctor_set(v___x_1049_, 6, v_currNamespace_1035_);
                crate::leanh::lean_ctor_set(v___x_1049_, 7, v_openDecls_1036_);
                crate::leanh::lean_ctor_set(v___x_1049_, 8, v_initHeartbeats_1037_);
                crate::leanh::lean_ctor_set(v___x_1049_, 9, v_maxHeartbeats_1038_);
                crate::leanh::lean_ctor_set(v___x_1049_, 10, v_quotContext_1039_);
                crate::leanh::lean_ctor_set(v___x_1049_, 11, v_currMacroScope_1040_);
                crate::leanh::lean_ctor_set(v___x_1049_, 12, v_cancelTk_x3f_1042_);
                crate::leanh::lean_ctor_set(v___x_1049_, 13, v_inheritedTraceOptions_1044_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1049_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_1041_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1049_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1043_,
                );
                v___x_1050_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1047_);
                crate::leanh::lean_dec_ref(v_traces_1047_);
                v_sz_1051_ = lean_array_size(v___x_1050_);
                v___x_1052_ = 0usize;
                v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__9(v_sz_1051_, v___x_1052_, v___x_1050_);
                v_msg_1054_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_1054_, 0, v_data_1023_);
                crate::leanh::lean_ctor_set(v_msg_1054_, 1, v_msg_1025_);
                crate::leanh::lean_ctor_set(v_msg_1054_, 2, v___x_1053_);
                v___x_1055_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7_spec__10(v_msg_1054_, v___x_1049_, v___y_1027_);
                crate::leanh::lean_dec_ref_known(v___x_1049_, 14);
                v_a_1056_ = crate::leanh::lean_ctor_get(v___x_1055_, 0);
                v_isSharedCheck_1093_ = (!crate::leanh::lean_is_exclusive(v___x_1055_)) as u8;
                if v_isSharedCheck_1093_ == 0 {
                    v___x_1058_ = v___x_1055_;
                    v_isShared_1059_ = v_isSharedCheck_1093_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1056_);
                    crate::leanh::lean_dec(v___x_1055_);
                    v___x_1058_ = crate::leanh::lean_box(0);
                    v_isShared_1059_ = v_isSharedCheck_1093_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1060_ = lean_st_ref_take(v___y_1027_);
                v_traceState_1061_ = crate::leanh::lean_ctor_get(v___x_1060_, 4);
                v_env_1062_ = crate::leanh::lean_ctor_get(v___x_1060_, 0);
                v_nextMacroScope_1063_ = crate::leanh::lean_ctor_get(v___x_1060_, 1);
                v_ngen_1064_ = crate::leanh::lean_ctor_get(v___x_1060_, 2);
                v_auxDeclNGen_1065_ = crate::leanh::lean_ctor_get(v___x_1060_, 3);
                v_cache_1066_ = crate::leanh::lean_ctor_get(v___x_1060_, 5);
                v_messages_1067_ = crate::leanh::lean_ctor_get(v___x_1060_, 6);
                v_infoState_1068_ = crate::leanh::lean_ctor_get(v___x_1060_, 7);
                v_snapshotTasks_1069_ = crate::leanh::lean_ctor_get(v___x_1060_, 8);
                v_isSharedCheck_1092_ = (!crate::leanh::lean_is_exclusive(v___x_1060_)) as u8;
                if v_isSharedCheck_1092_ == 0 {
                    v___x_1071_ = v___x_1060_;
                    v_isShared_1072_ = v_isSharedCheck_1092_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1069_);
                    crate::leanh::lean_inc(v_infoState_1068_);
                    crate::leanh::lean_inc(v_messages_1067_);
                    crate::leanh::lean_inc(v_cache_1066_);
                    crate::leanh::lean_inc(v_traceState_1061_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1065_);
                    crate::leanh::lean_inc(v_ngen_1064_);
                    crate::leanh::lean_inc(v_nextMacroScope_1063_);
                    crate::leanh::lean_inc(v_env_1062_);
                    crate::leanh::lean_dec(v___x_1060_);
                    v___x_1071_ = crate::leanh::lean_box(0);
                    v_isShared_1072_ = v_isSharedCheck_1092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1073_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1061_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1090_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1061_)) as u8;
                if v_isSharedCheck_1090_ == 0 {
                    v_unused_1091_ = crate::leanh::lean_ctor_get(v_traceState_1061_, 0);
                    crate::leanh::lean_dec(v_unused_1091_);
                    v___x_1075_ = v_traceState_1061_;
                    v_isShared_1076_ = v_isSharedCheck_1090_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_1061_);
                    v___x_1075_ = crate::leanh::lean_box(0);
                    v_isShared_1076_ = v_isSharedCheck_1090_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1077_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1077_, 0, v_ref_1024_);
                crate::leanh::lean_ctor_set(v___x_1077_, 1, v_a_1056_);
                v___x_1078_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1022_, v___x_1077_);
                if v_isShared_1076_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1075_, 0, v___x_1078_);
                    v___x_1080_ = v___x_1075_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1089_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1078_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1089_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1073_,
                    );
                    v___x_1080_ = v_reuseFailAlloc_1089_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1072_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1071_, 4, v___x_1080_);
                    v___x_1082_ = v___x_1071_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1088_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_env_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_nextMacroScope_1063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_ngen_1064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_auxDeclNGen_1065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 4, v___x_1080_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 5, v_cache_1066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 6, v_messages_1067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 7, v_infoState_1068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 8, v_snapshotTasks_1069_);
                    v___x_1082_ = v_reuseFailAlloc_1088_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1083_ = lean_st_ref_set(v___y_1027_, v___x_1082_);
                v___x_1084_ = crate::leanh::lean_box(0);
                if v_isShared_1059_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1058_, 0, v___x_1084_);
                    v___x_1086_ = v___x_1058_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
                    v___x_1086_ = v_reuseFailAlloc_1087_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7___boxed(
    mut v_oldTraces_1094_: *mut crate::leanh::LeanObject,
    mut v_data_1095_: *mut crate::leanh::LeanObject,
    mut v_ref_1096_: *mut crate::leanh::LeanObject,
    mut v_msg_1097_: *mut crate::leanh::LeanObject,
    mut v___y_1098_: *mut crate::leanh::LeanObject,
    mut v___y_1099_: *mut crate::leanh::LeanObject,
    mut v___y_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1101_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(v_oldTraces_1094_, v_data_1095_, v_ref_1096_, v_msg_1097_, v___y_1098_, v___y_1099_);
    crate::leanh::lean_dec(v___y_1099_);
    crate::leanh::lean_dec_ref(v___y_1098_);
    return v_res_1101_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(
    mut v_e_1102_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_1102_) == 0 {
        let mut v___x_1103_: u8 = 0;
        v___x_1103_ = 2;
        return v___x_1103_;
    } else {
        let mut v___x_1104_: u8 = 0;
        v___x_1104_ = 0;
        return v___x_1104_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6___boxed(
    mut v_e_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1106_: u8 = 0;
    let mut v_r_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1106_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_e_1105_);
    crate::leanh::lean_dec_ref(v_e_1105_);
    v_r_1107_ = crate::leanh::lean_box((v_res_1106_) as usize);
    return v_r_1107_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__0;
    v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
    return v___x_1110_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2()
-> f64 {
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: f64 = 0.0;
    v___x_1111_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1112_ = lean_float_of_nat(v___x_1111_);
    return v___x_1112_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__3;
    v___x_1115_ = l_Lean_stringToMessageData(v___x_1114_);
    return v___x_1115_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5()
-> f64 {
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: f64 = 0.0;
    v___x_1116_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_1117_ = lean_float_of_nat(v___x_1116_);
    return v___x_1117_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(
    mut v_cls_1118_: *mut crate::leanh::LeanObject,
    mut v_collapsed_1119_: u8,
    mut v_tag_1120_: *mut crate::leanh::LeanObject,
    mut v_opts_1121_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_1122_: u8,
    mut v_oldTraces_1123_: *mut crate::leanh::LeanObject,
    mut v_msg_1124_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_1125_: *mut crate::leanh::LeanObject,
    mut v___y_1126_: *mut crate::leanh::LeanObject,
    mut v___y_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1133_: u8 = 0;
    let mut v___y_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: u8 = 0;
    let mut v___y_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1150_: u8 = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: f64 = 0.0;
    let mut v_data_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: f64 = 0.0;
    let mut v___x_1164_: f64 = 0.0;
    let mut v_reuseFailAlloc_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1173_: u8 = 0;
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1186_: u8 = 0;
    let mut v_tid_1187_: u64 = 0;
    let mut v_traces_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1191_: u8 = 0;
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1201_: u8 = 0;
    let mut v_isSharedCheck_1202_: u8 = 0;
    let mut v___y_1204_: f64 = 0.0;
    let mut v___x_1205_: f64 = 0.0;
    let mut v___x_1206_: f64 = 0.0;
    let mut v___x_1207_: f64 = 0.0;
    let mut v___x_1208_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: f64 = 0.0;
    let mut v___x_1214_: f64 = 0.0;
    let mut v___x_1215_: f64 = 0.0;
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: f64 = 0.0;
    let mut v_isSharedCheck_1219_: u8 = 0;
    let mut v_isSharedCheck_1220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1129_ = crate::leanh::lean_ctor_get(v_resStartStop_1125_, 0);
                v_snd_1130_ = crate::leanh::lean_ctor_get(v_resStartStop_1125_, 1);
                v_isSharedCheck_1220_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_1125_)) as u8;
                if v_isSharedCheck_1220_ == 0 {
                    v___x_1132_ = v_resStartStop_1125_;
                    v_isShared_1133_ = v_isSharedCheck_1220_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1130_);
                    crate::leanh::lean_inc(v_fst_1129_);
                    crate::leanh::lean_dec(v_resStartStop_1125_);
                    v___x_1132_ = crate::leanh::lean_box(0);
                    v_isShared_1133_ = v_isSharedCheck_1220_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1140_ = crate::leanh::lean_ctor_get(v_snd_1130_, 0);
                v_snd_1141_ = crate::leanh::lean_ctor_get(v_snd_1130_, 1);
                v_isSharedCheck_1219_ = (!crate::leanh::lean_is_exclusive(v_snd_1130_)) as u8;
                if v_isSharedCheck_1219_ == 0 {
                    v___x_1143_ = v_snd_1130_;
                    v_isShared_1144_ = v_isSharedCheck_1219_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1141_);
                    crate::leanh::lean_inc(v_fst_1140_);
                    crate::leanh::lean_dec(v_snd_1130_);
                    v___x_1143_ = crate::leanh::lean_box(0);
                    v_isShared_1144_ = v_isSharedCheck_1219_;
                    state = 3;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_1135_);
                v___x_1138_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__7(v_oldTraces_1123_, v_data_1137_, v___y_1135_, v___y_1136_, v___y_1126_, v___y_1127_);
                if crate::leanh::lean_obj_tag(v___x_1138_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1138_, 1);
                    v___x_1139_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_fst_1129_);
                    return v___x_1139_;
                } else {
                    crate::leanh::lean_dec(v_fst_1129_);
                    return v___x_1138_;
                }
            }
            3 => {
                v___x_1145_ = l_Lean_trace_profiler;
                v___x_1146_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(
                    v_opts_1121_,
                    v___x_1145_,
                );
                if v___x_1146_ == 0 {
                    v___y_1173_ = v___x_1146_;
                    state = 8;
                    continue;
                } else {
                    v___x_1209_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_1210_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(
                        v_opts_1121_,
                        v___x_1209_,
                    );
                    if v___x_1210_ == 0 {
                        v___x_1211_ = l_Lean_trace_profiler_threshold;
                        v___x_1212_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(
                            v_opts_1121_,
                            v___x_1211_,
                        );
                        v___x_1213_ = lean_float_of_nat(v___x_1212_);
                        v___x_1214_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__5);
                        v___x_1215_ = lean_float_div(v___x_1213_, v___x_1214_);
                        v___y_1204_ = v___x_1215_;
                        state = 13;
                        continue;
                    } else {
                        v___x_1216_ = l_Lean_trace_profiler_threshold;
                        v___x_1217_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(
                            v_opts_1121_,
                            v___x_1216_,
                        );
                        v___x_1218_ = lean_float_of_nat(v___x_1217_);
                        v___y_1204_ = v___x_1218_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_result_1150_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__6(v_fst_1129_);
                v___x_1151_ = l_Lean_TraceResult_toEmoji(v_result_1150_);
                v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
                v___x_1153_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__1);
                if v_isShared_1144_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1143_, 7);
                    crate::leanh::lean_ctor_set(v___x_1143_, 1, v___x_1153_);
                    crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1152_);
                    v___x_1155_ = v___x_1143_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1153_);
                    v___x_1155_ = v_reuseFailAlloc_1166_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1133_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1132_, 7);
                    crate::leanh::lean_ctor_set(v___x_1132_, 1, v_a_1149_);
                    crate::leanh::lean_ctor_set(v___x_1132_, 0, v___x_1155_);
                    v_m_1157_ = v___x_1132_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1165_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_a_1149_);
                    v_m_1157_ = v_reuseFailAlloc_1165_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1158_ = crate::leanh::lean_box((v_result_1150_) as usize);
                v___x_1159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1159_, 0, v___x_1158_);
                v___x_1160_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__2);
                crate::leanh::lean_inc_ref(v_tag_1120_);
                crate::leanh::lean_inc_ref(v___x_1159_);
                crate::leanh::lean_inc(v_cls_1118_);
                v_data_1161_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_1161_, 0, v_cls_1118_);
                crate::leanh::lean_ctor_set(v_data_1161_, 1, v___x_1159_);
                crate::leanh::lean_ctor_set(v_data_1161_, 2, v_tag_1120_);
                crate::leanh::lean_ctor_set_float(
                    v_data_1161_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1160_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_1161_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1160_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_1161_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_1119_,
                );
                if v___x_1146_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1159_, 1);
                    crate::leanh::lean_dec(v_snd_1141_);
                    crate::leanh::lean_dec(v_fst_1140_);
                    crate::leanh::lean_dec_ref(v_tag_1120_);
                    crate::leanh::lean_dec(v_cls_1118_);
                    v___y_1135_ = v___y_1148_;
                    v___y_1136_ = v_m_1157_;
                    v_data_1137_ = v_data_1161_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_1161_, 3);
                    v_data_1162_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_1162_, 0, v_cls_1118_);
                    crate::leanh::lean_ctor_set(v_data_1162_, 1, v___x_1159_);
                    crate::leanh::lean_ctor_set(v_data_1162_, 2, v_tag_1120_);
                    v___x_1163_ = crate::leanh::lean_unbox_float(v_fst_1140_);
                    crate::leanh::lean_dec(v_fst_1140_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_1162_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_1163_,
                    );
                    v___x_1164_ = crate::leanh::lean_unbox_float(v_snd_1141_);
                    crate::leanh::lean_dec(v_snd_1141_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_1162_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_1164_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_1162_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_1119_,
                    );
                    v___y_1135_ = v___y_1148_;
                    v___y_1136_ = v_m_1157_;
                    v_data_1137_ = v_data_1162_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v_ref_1168_ = crate::leanh::lean_ctor_get(v___y_1126_, 5);
                crate::leanh::lean_inc(v___y_1127_);
                crate::leanh::lean_inc_ref(v___y_1126_);
                crate::leanh::lean_inc(v_fst_1129_);
                v___x_1169_ = crate::leanh::lean_apply_4(
                    v_msg_1124_,
                    v_fst_1129_,
                    v___y_1126_,
                    v___y_1127_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1169_) == 0 {
                    v_a_1170_ = crate::leanh::lean_ctor_get(v___x_1169_, 0);
                    crate::leanh::lean_inc(v_a_1170_);
                    crate::leanh::lean_dec_ref_known(v___x_1169_, 1);
                    v___y_1148_ = v_ref_1168_;
                    v_a_1149_ = v_a_1170_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1169_, 1);
                    v___x_1171_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___closed__4);
                    v___y_1148_ = v_ref_1168_;
                    v_a_1149_ = v___x_1171_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                if v_clsEnabled_1122_ == 0 {
                    if v___y_1173_ == 0 {
                        crate::leanh::lean_del_object(v___x_1143_);
                        crate::leanh::lean_dec(v_snd_1141_);
                        crate::leanh::lean_dec(v_fst_1140_);
                        crate::leanh::lean_del_object(v___x_1132_);
                        crate::leanh::lean_dec_ref(v_msg_1124_);
                        crate::leanh::lean_dec_ref(v_tag_1120_);
                        crate::leanh::lean_dec(v_cls_1118_);
                        v___x_1174_ = lean_st_ref_take(v___y_1127_);
                        v_traceState_1175_ = crate::leanh::lean_ctor_get(v___x_1174_, 4);
                        v_env_1176_ = crate::leanh::lean_ctor_get(v___x_1174_, 0);
                        v_nextMacroScope_1177_ = crate::leanh::lean_ctor_get(v___x_1174_, 1);
                        v_ngen_1178_ = crate::leanh::lean_ctor_get(v___x_1174_, 2);
                        v_auxDeclNGen_1179_ = crate::leanh::lean_ctor_get(v___x_1174_, 3);
                        v_cache_1180_ = crate::leanh::lean_ctor_get(v___x_1174_, 5);
                        v_messages_1181_ = crate::leanh::lean_ctor_get(v___x_1174_, 6);
                        v_infoState_1182_ = crate::leanh::lean_ctor_get(v___x_1174_, 7);
                        v_snapshotTasks_1183_ = crate::leanh::lean_ctor_get(v___x_1174_, 8);
                        v_isSharedCheck_1202_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1174_)) as u8;
                        if v_isSharedCheck_1202_ == 0 {
                            v___x_1185_ = v___x_1174_;
                            v_isShared_1186_ = v_isSharedCheck_1202_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_1183_);
                            crate::leanh::lean_inc(v_infoState_1182_);
                            crate::leanh::lean_inc(v_messages_1181_);
                            crate::leanh::lean_inc(v_cache_1180_);
                            crate::leanh::lean_inc(v_traceState_1175_);
                            crate::leanh::lean_inc(v_auxDeclNGen_1179_);
                            crate::leanh::lean_inc(v_ngen_1178_);
                            crate::leanh::lean_inc(v_nextMacroScope_1177_);
                            crate::leanh::lean_inc(v_env_1176_);
                            crate::leanh::lean_dec(v___x_1174_);
                            v___x_1185_ = crate::leanh::lean_box(0);
                            v_isShared_1186_ = v_isSharedCheck_1202_;
                            state = 9;
                            continue;
                        }
                    } else {
                        state = 7;
                        continue;
                    }
                } else {
                    state = 7;
                    continue;
                }
            }
            9 => {
                v_tid_1187_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1175_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1188_ = crate::leanh::lean_ctor_get(v_traceState_1175_, 0);
                v_isSharedCheck_1201_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1175_)) as u8;
                if v_isSharedCheck_1201_ == 0 {
                    v___x_1190_ = v_traceState_1175_;
                    v_isShared_1191_ = v_isSharedCheck_1201_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1188_);
                    crate::leanh::lean_dec(v_traceState_1175_);
                    v___x_1190_ = crate::leanh::lean_box(0);
                    v_isShared_1191_ = v_isSharedCheck_1201_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1192_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_1123_, v_traces_1188_);
                crate::leanh::lean_dec_ref(v_traces_1188_);
                if v_isShared_1191_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1190_, 0, v___x_1192_);
                    v___x_1194_ = v___x_1190_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1200_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1192_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1200_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1187_,
                    );
                    v___x_1194_ = v_reuseFailAlloc_1200_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1186_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1185_, 4, v___x_1194_);
                    v___x_1196_ = v___x_1185_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1199_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_env_1176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_nextMacroScope_1177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_ngen_1178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 3, v_auxDeclNGen_1179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 4, v___x_1194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 5, v_cache_1180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 6, v_messages_1181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 7, v_infoState_1182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 8, v_snapshotTasks_1183_);
                    v___x_1196_ = v_reuseFailAlloc_1199_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1197_ = lean_st_ref_set(v___y_1127_, v___x_1196_);
                v___x_1198_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_fst_1129_);
                return v___x_1198_;
            }
            13 => {
                v___x_1205_ = crate::leanh::lean_unbox_float(v_snd_1141_);
                v___x_1206_ = crate::leanh::lean_unbox_float(v_fst_1140_);
                v___x_1207_ = lean_float_sub(v___x_1205_, v___x_1206_);
                v___x_1208_ = lean_float_decLt(v___y_1204_, v___x_1207_);
                v___y_1173_ = v___x_1208_;
                state = 8;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5___boxed(
    mut v_cls_1221_: *mut crate::leanh::LeanObject,
    mut v_collapsed_1222_: *mut crate::leanh::LeanObject,
    mut v_tag_1223_: *mut crate::leanh::LeanObject,
    mut v_opts_1224_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_1225_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_1226_: *mut crate::leanh::LeanObject,
    mut v_msg_1227_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_1232_: u8 = 0;
    let mut v_clsEnabled_boxed_1233_: u8 = 0;
    let mut v_res_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_1232_ = (crate::leanh::lean_unbox(v_collapsed_1222_) as u8);
    v_clsEnabled_boxed_1233_ = (crate::leanh::lean_unbox(v_clsEnabled_1225_) as u8);
    v_res_1234_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v_cls_1221_, v_collapsed_boxed_1232_, v_tag_1223_, v_opts_1224_, v_clsEnabled_boxed_1233_, v_oldTraces_1226_, v_msg_1227_, v_resStartStop_1228_, v___y_1229_, v___y_1230_);
    crate::leanh::lean_dec(v___y_1230_);
    crate::leanh::lean_dec_ref(v___y_1229_);
    crate::leanh::lean_dec_ref(v_opts_1224_);
    return v_res_1234_;
}
pub unsafe fn _init_l_Lean_Compiler_compile___lam__1___closed__0() -> f64 {
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: f64 = 0.0;
    v___x_1235_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_1236_ = lean_float_of_nat(v___x_1235_);
    return v___x_1236_;
}
pub unsafe fn _init_l_Lean_Compiler_compile___lam__1___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1237_;
}
pub unsafe fn _init_l_Lean_Compiler_compile___lam__1___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__1___closed__1_once),
        _init_l_Lean_Compiler_compile___lam__1___closed__1,
    );
    v___x_1239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    return v___x_1239_;
}
pub unsafe fn _init_l_Lean_Compiler_compile___lam__1___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1240_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__1___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__1___closed__2_once),
        _init_l_Lean_Compiler_compile___lam__1___closed__2,
    );
    v___x_1241_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1241_, 0, v___x_1240_);
    crate::leanh::lean_ctor_set(v___x_1241_, 1, v___x_1240_);
    return v___x_1241_;
}
pub unsafe fn l_Lean_Compiler_compile___lam__1(
    mut v___x_1242_: *mut crate::leanh::LeanObject,
    mut v___x_1243_: u8,
    mut v___x_1244_: *mut crate::leanh::LeanObject,
    mut v___f_1245_: *mut crate::leanh::LeanObject,
    mut v_declNames_1246_: *mut crate::leanh::LeanObject,
    mut v___x_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
    mut v___y_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1264_: u8 = 0;
    let mut v_inheritedTraceOptions_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1268_: u8 = 0;
    let mut v_env_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1274_: u8 = 0;
    let mut v___y_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: f64 = 0.0;
    let mut v___x_1282_: f64 = 0.0;
    let mut v___x_1283_: f64 = 0.0;
    let mut v___x_1284_: f64 = 0.0;
    let mut v___x_1285_: f64 = 0.0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1292_: u8 = 0;
    let mut v___y_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: f64 = 0.0;
    let mut v___x_1300_: f64 = 0.0;
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1307_: u8 = 0;
    let mut v___y_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: u8 = 0;
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut v_a_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1327_: u8 = 0;
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1331_: u8 = 0;
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1341_: u8 = 0;
    let mut v_a_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v_fileName_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1364_: u8 = 0;
    let mut v_inheritedTraceOptions_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1367_: u8 = 0;
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1381_: u8 = 0;
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1400_: u8 = 0;
    let mut v_unused_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: u8 = 0;
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut v_unused_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1251_ = lean_st_ref_get(v___y_1249_);
                v_fileName_1252_ = crate::leanh::lean_ctor_get(v___y_1248_, 0);
                v_fileMap_1253_ = crate::leanh::lean_ctor_get(v___y_1248_, 1);
                v_options_1254_ = crate::leanh::lean_ctor_get(v___y_1248_, 2);
                v_currRecDepth_1255_ = crate::leanh::lean_ctor_get(v___y_1248_, 3);
                v_ref_1256_ = crate::leanh::lean_ctor_get(v___y_1248_, 5);
                v_currNamespace_1257_ = crate::leanh::lean_ctor_get(v___y_1248_, 6);
                v_openDecls_1258_ = crate::leanh::lean_ctor_get(v___y_1248_, 7);
                v_initHeartbeats_1259_ = crate::leanh::lean_ctor_get(v___y_1248_, 8);
                v_maxHeartbeats_1260_ = crate::leanh::lean_ctor_get(v___y_1248_, 9);
                v_quotContext_1261_ = crate::leanh::lean_ctor_get(v___y_1248_, 10);
                v_currMacroScope_1262_ = crate::leanh::lean_ctor_get(v___y_1248_, 11);
                v_cancelTk_x3f_1263_ = crate::leanh::lean_ctor_get(v___y_1248_, 12);
                v_suppressElabErrors_1264_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1248_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1265_ = crate::leanh::lean_ctor_get(v___y_1248_, 13);
                v_isSharedCheck_1403_ = (!crate::leanh::lean_is_exclusive(v___y_1248_)) as u8;
                if v_isSharedCheck_1403_ == 0 {
                    v_unused_1404_ = crate::leanh::lean_ctor_get(v___y_1248_, 4);
                    crate::leanh::lean_dec(v_unused_1404_);
                    v___x_1267_ = v___y_1248_;
                    v_isShared_1268_ = v_isSharedCheck_1403_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inheritedTraceOptions_1265_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_1263_);
                    crate::leanh::lean_inc(v_currMacroScope_1262_);
                    crate::leanh::lean_inc(v_quotContext_1261_);
                    crate::leanh::lean_inc(v_maxHeartbeats_1260_);
                    crate::leanh::lean_inc(v_initHeartbeats_1259_);
                    crate::leanh::lean_inc(v_openDecls_1258_);
                    crate::leanh::lean_inc(v_currNamespace_1257_);
                    crate::leanh::lean_inc(v_ref_1256_);
                    crate::leanh::lean_inc(v_currRecDepth_1255_);
                    crate::leanh::lean_inc(v_options_1254_);
                    crate::leanh::lean_inc(v_fileMap_1253_);
                    crate::leanh::lean_inc(v_fileName_1252_);
                    crate::leanh::lean_dec(v___y_1248_);
                    v___x_1267_ = crate::leanh::lean_box(0);
                    v_isShared_1268_ = v_isSharedCheck_1403_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_env_1269_ = crate::leanh::lean_ctor_get(v___x_1251_, 0);
                crate::leanh::lean_inc_ref(v_env_1269_);
                crate::leanh::lean_dec(v___x_1251_);
                v___x_1270_ = l_Lean_Compiler_compiler_postponeCompile;
                v___x_1271_ = 0;
                v___x_1272_ = l_Lean_Option_set___at___00Lean_Compiler_compile_spec__1(
                    v_options_1254_,
                    v___x_1270_,
                    v___x_1271_,
                );
                v___x_1350_ = l_Lean_diagnostics;
                v___x_1351_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(
                    v___x_1272_,
                    v___x_1350_,
                );
                v___x_1402_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1269_);
                crate::leanh::lean_dec_ref(v_env_1269_);
                if v___x_1402_ == 0 {
                    if v___x_1351_ == 0 {
                        v_fileName_1353_ = v_fileName_1252_;
                        v_fileMap_1354_ = v_fileMap_1253_;
                        v_currRecDepth_1355_ = v_currRecDepth_1255_;
                        v_ref_1356_ = v_ref_1256_;
                        v_currNamespace_1357_ = v_currNamespace_1257_;
                        v_openDecls_1358_ = v_openDecls_1258_;
                        v_initHeartbeats_1359_ = v_initHeartbeats_1259_;
                        v_maxHeartbeats_1360_ = v_maxHeartbeats_1260_;
                        v_quotContext_1361_ = v_quotContext_1261_;
                        v_currMacroScope_1362_ = v_currMacroScope_1262_;
                        v_cancelTk_x3f_1363_ = v_cancelTk_x3f_1263_;
                        v_suppressElabErrors_1364_ = v_suppressElabErrors_1264_;
                        v_inheritedTraceOptions_1365_ = v_inheritedTraceOptions_1265_;
                        v___y_1366_ = v___y_1249_;
                        state = 13;
                        continue;
                    } else {
                        v___y_1381_ = v___x_1402_;
                        state = 15;
                        continue;
                    }
                } else {
                    v___y_1381_ = v___x_1351_;
                    state = 15;
                    continue;
                }
            }
            2 => {
                v___x_1280_ = lean_io_mono_nanos_now();
                v___x_1281_ = lean_float_of_nat(v___y_1278_);
                v___x_1282_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__1___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__1___closed__0_once),
                    _init_l_Lean_Compiler_compile___lam__1___closed__0,
                );
                v___x_1283_ = lean_float_div(v___x_1281_, v___x_1282_);
                v___x_1284_ = lean_float_of_nat(v___x_1280_);
                v___x_1285_ = lean_float_div(v___x_1284_, v___x_1282_);
                v___x_1286_ = crate::leanh::lean_box_float(v___x_1283_);
                v___x_1287_ = crate::leanh::lean_box_float(v___x_1285_);
                v___x_1288_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1288_, 0, v___x_1286_);
                crate::leanh::lean_ctor_set(v___x_1288_, 1, v___x_1287_);
                v___x_1289_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1289_, 0, v_a_1279_);
                crate::leanh::lean_ctor_set(v___x_1289_, 1, v___x_1288_);
                v___x_1290_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_1242_, v___x_1243_, v___x_1244_, v___x_1272_, v___y_1274_, v___y_1276_, v___f_1245_, v___x_1289_, v___y_1275_, v___y_1277_);
                crate::leanh::lean_dec_ref(v___y_1275_);
                crate::leanh::lean_dec_ref(v___x_1272_);
                return v___x_1290_;
            }
            3 => {
                v___x_1298_ = lean_io_get_num_heartbeats();
                v___x_1299_ = lean_float_of_nat(v___y_1296_);
                v___x_1300_ = lean_float_of_nat(v___x_1298_);
                v___x_1301_ = crate::leanh::lean_box_float(v___x_1299_);
                v___x_1302_ = crate::leanh::lean_box_float(v___x_1300_);
                v___x_1303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1303_, 0, v___x_1301_);
                crate::leanh::lean_ctor_set(v___x_1303_, 1, v___x_1302_);
                v___x_1304_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1304_, 0, v_a_1297_);
                crate::leanh::lean_ctor_set(v___x_1304_, 1, v___x_1303_);
                v___x_1305_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5(v___x_1242_, v___x_1243_, v___x_1244_, v___x_1272_, v___y_1292_, v___y_1294_, v___f_1245_, v___x_1304_, v___y_1293_, v___y_1295_);
                crate::leanh::lean_dec_ref(v___y_1293_);
                crate::leanh::lean_dec_ref(v___x_1272_);
                return v___x_1305_;
            }
            4 => {
                v___x_1310_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Compiler_compile_spec__4___redArg(v___y_1309_);
                v_a_1311_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                crate::leanh::lean_inc(v_a_1311_);
                crate::leanh::lean_dec_ref(v___x_1310_);
                v___x_1312_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_1313_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(
                    v___x_1272_,
                    v___x_1312_,
                );
                if v___x_1313_ == 0 {
                    v___x_1314_ = lean_io_mono_nanos_now();
                    v___x_1315_ = l_Lean_Compiler_LCNF_main(
                        v_declNames_1246_,
                        v___x_1247_,
                        v___y_1308_,
                        v___y_1309_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1315_) == 0 {
                        v_a_1316_ = crate::leanh::lean_ctor_get(v___x_1315_, 0);
                        v_isSharedCheck_1323_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1315_)) as u8;
                        if v_isSharedCheck_1323_ == 0 {
                            v___x_1318_ = v___x_1315_;
                            v_isShared_1319_ = v_isSharedCheck_1323_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1316_);
                            crate::leanh::lean_dec(v___x_1315_);
                            v___x_1318_ = crate::leanh::lean_box(0);
                            v_isShared_1319_ = v_isSharedCheck_1323_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1324_ = crate::leanh::lean_ctor_get(v___x_1315_, 0);
                        v_isSharedCheck_1331_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1315_)) as u8;
                        if v_isSharedCheck_1331_ == 0 {
                            v___x_1326_ = v___x_1315_;
                            v_isShared_1327_ = v_isSharedCheck_1331_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1324_);
                            crate::leanh::lean_dec(v___x_1315_);
                            v___x_1326_ = crate::leanh::lean_box(0);
                            v_isShared_1327_ = v_isSharedCheck_1331_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_1332_ = lean_io_get_num_heartbeats();
                    v___x_1333_ = l_Lean_Compiler_LCNF_main(
                        v_declNames_1246_,
                        v___x_1247_,
                        v___y_1308_,
                        v___y_1309_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1333_) == 0 {
                        v_a_1334_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                        v_isSharedCheck_1341_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1333_)) as u8;
                        if v_isSharedCheck_1341_ == 0 {
                            v___x_1336_ = v___x_1333_;
                            v_isShared_1337_ = v_isSharedCheck_1341_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1334_);
                            crate::leanh::lean_dec(v___x_1333_);
                            v___x_1336_ = crate::leanh::lean_box(0);
                            v_isShared_1337_ = v_isSharedCheck_1341_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_1342_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                        v_isSharedCheck_1349_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1333_)) as u8;
                        if v_isSharedCheck_1349_ == 0 {
                            v___x_1344_ = v___x_1333_;
                            v_isShared_1345_ = v_isSharedCheck_1349_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1342_);
                            crate::leanh::lean_dec(v___x_1333_);
                            v___x_1344_ = crate::leanh::lean_box(0);
                            v_isShared_1345_ = v_isSharedCheck_1349_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_1319_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1318_, 1);
                    v___x_1321_ = v___x_1318_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
                    v___x_1321_ = v_reuseFailAlloc_1322_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_1274_ = v___y_1307_;
                v___y_1275_ = v___y_1308_;
                v___y_1276_ = v_a_1311_;
                v___y_1277_ = v___y_1309_;
                v___y_1278_ = v___x_1314_;
                v_a_1279_ = v___x_1321_;
                state = 2;
                continue;
            }
            7 => {
                if v_isShared_1327_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1326_, 0);
                    v___x_1329_ = v___x_1326_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
                    v___x_1329_ = v_reuseFailAlloc_1330_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_1274_ = v___y_1307_;
                v___y_1275_ = v___y_1308_;
                v___y_1276_ = v_a_1311_;
                v___y_1277_ = v___y_1309_;
                v___y_1278_ = v___x_1314_;
                v_a_1279_ = v___x_1329_;
                state = 2;
                continue;
            }
            9 => {
                if v_isShared_1337_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1336_, 1);
                    v___x_1339_ = v___x_1336_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
                    v___x_1339_ = v_reuseFailAlloc_1340_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_1292_ = v___y_1307_;
                v___y_1293_ = v___y_1308_;
                v___y_1294_ = v_a_1311_;
                v___y_1295_ = v___y_1309_;
                v___y_1296_ = v___x_1332_;
                v_a_1297_ = v___x_1339_;
                state = 3;
                continue;
            }
            11 => {
                if v_isShared_1345_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1344_, 0);
                    v___x_1347_ = v___x_1344_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1348_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
                    v___x_1347_ = v_reuseFailAlloc_1348_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_1292_ = v___y_1307_;
                v___y_1293_ = v___y_1308_;
                v___y_1294_ = v_a_1311_;
                v___y_1295_ = v___y_1309_;
                v___y_1296_ = v___x_1332_;
                v_a_1297_ = v___x_1347_;
                state = 3;
                continue;
            }
            13 => {
                v_hasTrace_1367_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1272_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_1368_ = l_Lean_maxRecDepth;
                v___x_1369_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__3(
                    v___x_1272_,
                    v___x_1368_,
                );
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1365_);
                crate::leanh::lean_inc_ref(v___x_1272_);
                if v_isShared_1268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1267_, 13, v_inheritedTraceOptions_1365_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 12, v_cancelTk_x3f_1363_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 11, v_currMacroScope_1362_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 10, v_quotContext_1361_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 9, v_maxHeartbeats_1360_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 8, v_initHeartbeats_1359_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 7, v_openDecls_1358_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 6, v_currNamespace_1357_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 5, v_ref_1356_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 4, v___x_1369_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 3, v_currRecDepth_1355_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 2, v___x_1272_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 1, v_fileMap_1354_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v_fileName_1353_);
                    v___x_1371_ = v___x_1267_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1379_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_fileName_1353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_fileMap_1354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 2, v___x_1272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_currRecDepth_1355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 4, v___x_1369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 5, v_ref_1356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 6, v_currNamespace_1357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 7, v_openDecls_1358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 8, v_initHeartbeats_1359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 9, v_maxHeartbeats_1360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 10, v_quotContext_1361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 11, v_currMacroScope_1362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 12, v_cancelTk_x3f_1363_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1379_,
                        13,
                        v_inheritedTraceOptions_1365_,
                    );
                    v___x_1371_ = v_reuseFailAlloc_1379_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1371_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___x_1351_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1371_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1364_,
                );
                if v_hasTrace_1367_ == 0 {
                    crate::leanh::lean_dec_ref(v_inheritedTraceOptions_1365_);
                    crate::leanh::lean_dec_ref(v___x_1272_);
                    crate::leanh::lean_dec_ref(v___f_1245_);
                    crate::leanh::lean_dec_ref(v___x_1244_);
                    crate::leanh::lean_dec(v___x_1242_);
                    v___x_1372_ = l_Lean_Compiler_LCNF_main(
                        v_declNames_1246_,
                        v___x_1247_,
                        v___x_1371_,
                        v___y_1366_,
                    );
                    crate::leanh::lean_dec_ref(v___x_1371_);
                    return v___x_1372_;
                } else {
                    v___x_1373_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_compile_spec__1_spec__1___closed__1;
                    crate::leanh::lean_inc(v___x_1242_);
                    v___x_1374_ = l_Lean_Name_append(v___x_1373_, v___x_1242_);
                    v___x_1375_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_1365_,
                        v___x_1272_,
                        v___x_1374_,
                    );
                    crate::leanh::lean_dec(v___x_1374_);
                    crate::leanh::lean_dec_ref(v_inheritedTraceOptions_1365_);
                    if v___x_1375_ == 0 {
                        v___x_1376_ = l_Lean_trace_profiler;
                        v___x_1377_ = l_Lean_Option_get___at___00Lean_Compiler_compile_spec__2(
                            v___x_1272_,
                            v___x_1376_,
                        );
                        if v___x_1377_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1272_);
                            crate::leanh::lean_dec_ref(v___f_1245_);
                            crate::leanh::lean_dec_ref(v___x_1244_);
                            crate::leanh::lean_dec(v___x_1242_);
                            v___x_1378_ = l_Lean_Compiler_LCNF_main(
                                v_declNames_1246_,
                                v___x_1247_,
                                v___x_1371_,
                                v___y_1366_,
                            );
                            crate::leanh::lean_dec_ref(v___x_1371_);
                            return v___x_1378_;
                        } else {
                            v___y_1307_ = v___x_1375_;
                            v___y_1308_ = v___x_1371_;
                            v___y_1309_ = v___y_1366_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_1307_ = v___x_1375_;
                        v___y_1308_ = v___x_1371_;
                        v___y_1309_ = v___y_1366_;
                        state = 4;
                        continue;
                    }
                }
            }
            15 => {
                if v___y_1381_ == 0 {
                    v___x_1382_ = lean_st_ref_take(v___y_1249_);
                    v_env_1383_ = crate::leanh::lean_ctor_get(v___x_1382_, 0);
                    v_nextMacroScope_1384_ = crate::leanh::lean_ctor_get(v___x_1382_, 1);
                    v_ngen_1385_ = crate::leanh::lean_ctor_get(v___x_1382_, 2);
                    v_auxDeclNGen_1386_ = crate::leanh::lean_ctor_get(v___x_1382_, 3);
                    v_traceState_1387_ = crate::leanh::lean_ctor_get(v___x_1382_, 4);
                    v_messages_1388_ = crate::leanh::lean_ctor_get(v___x_1382_, 6);
                    v_infoState_1389_ = crate::leanh::lean_ctor_get(v___x_1382_, 7);
                    v_snapshotTasks_1390_ = crate::leanh::lean_ctor_get(v___x_1382_, 8);
                    v_isSharedCheck_1400_ = (!crate::leanh::lean_is_exclusive(v___x_1382_)) as u8;
                    if v_isSharedCheck_1400_ == 0 {
                        v_unused_1401_ = crate::leanh::lean_ctor_get(v___x_1382_, 5);
                        crate::leanh::lean_dec(v_unused_1401_);
                        v___x_1392_ = v___x_1382_;
                        v_isShared_1393_ = v_isSharedCheck_1400_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_1390_);
                        crate::leanh::lean_inc(v_infoState_1389_);
                        crate::leanh::lean_inc(v_messages_1388_);
                        crate::leanh::lean_inc(v_traceState_1387_);
                        crate::leanh::lean_inc(v_auxDeclNGen_1386_);
                        crate::leanh::lean_inc(v_ngen_1385_);
                        crate::leanh::lean_inc(v_nextMacroScope_1384_);
                        crate::leanh::lean_inc(v_env_1383_);
                        crate::leanh::lean_dec(v___x_1382_);
                        v___x_1392_ = crate::leanh::lean_box(0);
                        v_isShared_1393_ = v_isSharedCheck_1400_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_fileName_1353_ = v_fileName_1252_;
                    v_fileMap_1354_ = v_fileMap_1253_;
                    v_currRecDepth_1355_ = v_currRecDepth_1255_;
                    v_ref_1356_ = v_ref_1256_;
                    v_currNamespace_1357_ = v_currNamespace_1257_;
                    v_openDecls_1358_ = v_openDecls_1258_;
                    v_initHeartbeats_1359_ = v_initHeartbeats_1259_;
                    v_maxHeartbeats_1360_ = v_maxHeartbeats_1260_;
                    v_quotContext_1361_ = v_quotContext_1261_;
                    v_currMacroScope_1362_ = v_currMacroScope_1262_;
                    v_cancelTk_x3f_1363_ = v_cancelTk_x3f_1263_;
                    v_suppressElabErrors_1364_ = v_suppressElabErrors_1264_;
                    v_inheritedTraceOptions_1365_ = v_inheritedTraceOptions_1265_;
                    v___y_1366_ = v___y_1249_;
                    state = 13;
                    continue;
                }
            }
            16 => {
                v___x_1394_ = l_Lean_Kernel_enableDiag(v_env_1383_, v___x_1351_);
                v___x_1395_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__1___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_compile___lam__1___closed__3_once),
                    _init_l_Lean_Compiler_compile___lam__1___closed__3,
                );
                if v_isShared_1393_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1392_, 5, v___x_1395_);
                    crate::leanh::lean_ctor_set(v___x_1392_, 0, v___x_1394_);
                    v___x_1397_ = v___x_1392_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1399_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_nextMacroScope_1384_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_ngen_1385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_auxDeclNGen_1386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_traceState_1387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 5, v___x_1395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 6, v_messages_1388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 7, v_infoState_1389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 8, v_snapshotTasks_1390_);
                    v___x_1397_ = v_reuseFailAlloc_1399_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1398_ = lean_st_ref_set(v___y_1249_, v___x_1397_);
                v_fileName_1353_ = v_fileName_1252_;
                v_fileMap_1354_ = v_fileMap_1253_;
                v_currRecDepth_1355_ = v_currRecDepth_1255_;
                v_ref_1356_ = v_ref_1256_;
                v_currNamespace_1357_ = v_currNamespace_1257_;
                v_openDecls_1358_ = v_openDecls_1258_;
                v_initHeartbeats_1359_ = v_initHeartbeats_1259_;
                v_maxHeartbeats_1360_ = v_maxHeartbeats_1260_;
                v_quotContext_1361_ = v_quotContext_1261_;
                v_currMacroScope_1362_ = v_currMacroScope_1262_;
                v_cancelTk_x3f_1363_ = v_cancelTk_x3f_1263_;
                v_suppressElabErrors_1364_ = v_suppressElabErrors_1264_;
                v_inheritedTraceOptions_1365_ = v_inheritedTraceOptions_1265_;
                v___y_1366_ = v___y_1249_;
                state = 13;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_compile___lam__1___boxed(
    mut v___x_1405_: *mut crate::leanh::LeanObject,
    mut v___x_1406_: *mut crate::leanh::LeanObject,
    mut v___x_1407_: *mut crate::leanh::LeanObject,
    mut v___f_1408_: *mut crate::leanh::LeanObject,
    mut v_declNames_1409_: *mut crate::leanh::LeanObject,
    mut v___x_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
    mut v___y_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7049__boxed_1414_: u8 = 0;
    let mut v_res_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7049__boxed_1414_ = (crate::leanh::lean_unbox(v___x_1406_) as u8);
    v_res_1415_ = l_Lean_Compiler_compile___lam__1(
        v___x_1405_,
        v___x_7049__boxed_1414_,
        v___x_1407_,
        v___f_1408_,
        v_declNames_1409_,
        v___x_1410_,
        v___y_1411_,
        v___y_1412_,
    );
    crate::leanh::lean_dec(v___y_1412_);
    return v_res_1415_;
}
pub unsafe fn l_Lean_Compiler_compile(
    mut v_declNames_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: u8 = 0;
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_1425_ = crate::leanh::lean_ctor_get(v_a_1422_, 2);
    crate::leanh::lean_inc_ref(v_declNames_1421_);
    v___f_1426_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_compile___lam__0___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1426_, 0, v_declNames_1421_);
    v___x_1427_ = l_Lean_Compiler_compile___closed__0;
    v___x_1428_ = l_Lean_Compiler_compile___closed__2;
    v___x_1429_ = l_Lean_Options_empty;
    v___x_1430_ = 1;
    v___x_1431_ = l_Lean_Compiler_compile___closed__3;
    v___x_1432_ = crate::leanh::lean_box((v___x_1430_) as usize);
    v___f_1433_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_compile___lam__1___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1433_, 0, v___x_1428_);
    crate::leanh::lean_closure_set(v___f_1433_, 1, v___x_1432_);
    crate::leanh::lean_closure_set(v___f_1433_, 2, v___x_1431_);
    crate::leanh::lean_closure_set(v___f_1433_, 3, v___f_1426_);
    crate::leanh::lean_closure_set(v___f_1433_, 4, v_declNames_1421_);
    crate::leanh::lean_closure_set(v___f_1433_, 5, v___x_1429_);
    v___x_1434_ = crate::leanh::lean_box(0);
    v___x_1435_ = l_Lean_profileitM___at___00Lean_Compiler_compile_spec__6___redArg(
        v___x_1427_,
        v_options_1425_,
        v___f_1433_,
        v___x_1434_,
        v_a_1422_,
        v_a_1423_,
    );
    return v___x_1435_;
}
pub unsafe fn l_Lean_Compiler_compile___boxed(
    mut v_declNames_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_Lean_Compiler_compile(v_declNames_1436_, v_a_1437_, v_a_1438_);
    crate::leanh::lean_dec(v_a_1438_);
    crate::leanh::lean_dec_ref(v_a_1437_);
    return v_res_1440_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(
    mut v_00_u03b1_1441_: *mut crate::leanh::LeanObject,
    mut v_x_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___redArg(v_x_1442_);
    return v___x_1446_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8___boxed(
    mut v_00_u03b1_1447_: *mut crate::leanh::LeanObject,
    mut v_x_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Compiler_compile_spec__5_spec__8(v_00_u03b1_1447_, v_x_1448_, v___y_1449_, v___y_1450_);
    crate::leanh::lean_dec(v___y_1450_);
    crate::leanh::lean_dec_ref(v___y_1449_);
    return v_res_1452_;
}
pub unsafe fn l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_Compiler_compile___closed__2;
    v___x_1514_ = 0;
    v___x_1515_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_;
    v___x_1516_ = l_Lean_registerTraceClass(v___x_1513_, v___x_1514_, v___x_1515_);
    if crate::leanh::lean_obj_tag(v___x_1516_) == 0 {
        let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_1516_, 1);
        v___x_1517_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_;
        v___x_1518_ = l_Lean_registerTraceClass(v___x_1517_, v___x_1514_, v___x_1515_);
        return v___x_1518_;
    } else {
        return v___x_1516_;
    }
}
pub unsafe fn l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2____boxed(
    mut v_a_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1520_ = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
    return v_res_1520_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_Main(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_Main_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Main_509999922____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_Main(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_Main(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_Main(builtin);
}

// Lean compiler output
// Module: Lean.ReservedNameAction
// Imports: Init.Control.Do Lean.CoreM
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    initialize_Lean_CoreM, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed, l_Lean_Exception_isRuntime,
    runtime_initialize_Lean_CoreM,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_containsOnBranch,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData,
    l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::ImportingFlag::l_Lean_initializing;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_backward_privateInPublic_warn, l_Lean_ResolveName_resolveGlobalName,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_registerTraceClass, l_Lean_trace_profiler, l_Lean_trace_profiler_threshold,
    l_Lean_trace_profiler_useHeartbeats,
};
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::ffi::lean_string_push;
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_usize_dec_eq,
};
use crate::ffi::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_expr_dbg_to_string;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_registerReservedNameAction___closed__0_value: crate::leanh::LeanStringObject<
    109,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 109,
    m_capacity: 109,
    m_length: 108,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32,
        114, 101, 115, 101, 114, 118, 101, 100, 32, 110, 97, 109, 101, 32, 97, 99, 116, 105, 111,
        110, 44, 32, 116, 104, 105, 115, 32, 107, 105, 110, 100, 32, 111, 102, 32, 101, 120, 116,
        101, 110, 115, 105, 111, 110, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32,
        114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32,
        105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_registerReservedNameAction___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerReservedNameAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_registerReservedNameAction___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerReservedNameAction___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_executeReservedNameAction___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        101, 120, 101, 99, 117, 116, 101, 82, 101, 115, 101, 114, 118, 101, 100, 78, 97, 109, 101,
        65, 99, 116, 105, 111, 110, 32, 102, 111, 114, 32, 0,
    ],
};
static mut l_Lean_executeReservedNameAction___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_executeReservedNameAction___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_executeReservedNameAction___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_executeReservedNameAction___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5: f64 = 0.0;
pub static l_Lean_executeReservedNameAction___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            82, 101, 115, 101, 114, 118, 101, 100, 78, 97, 109, 101, 65, 99, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_executeReservedNameAction___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_executeReservedNameAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_executeReservedNameAction___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_executeReservedNameAction___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16524425170056508783 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_executeReservedNameAction___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_executeReservedNameAction___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_executeReservedNameAction___closed__2_value: crate::leanh::LeanStringObject<1> =
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
static mut l_Lean_executeReservedNameAction___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_executeReservedNameAction___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_executeReservedNameAction___closed__3_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_executeReservedNameAction___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_executeReservedNameAction___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_executeReservedNameAction___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_executeReservedNameAction___closed__3_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_executeReservedNameAction___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_executeReservedNameAction___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_executeReservedNameAction___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_executeReservedNameAction___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_executeReservedNameAction___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_executeReservedNameAction___closed__6: f64 = 0.0;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 97, 108, 105, 122, 101, 32, 99,
        111, 110, 115, 116, 97, 110, 116, 32, 0,
    ],
};
static mut l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2_value:
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
    m_data: [58, 0],
};
static mut l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [80, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2_value: crate::leanh::LeanStringObject<167> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 167, m_capacity: 167, m_length: 166, m_data: [96, 32, 97, 99, 99, 101, 115, 115, 101, 100, 32, 112, 117, 98, 108, 105, 99, 108, 121, 59, 32, 116, 104, 105, 115, 32, 105, 115, 32, 97, 108, 108, 111, 119, 101, 100, 32, 111, 110, 108, 121, 32, 98, 101, 99, 97, 117, 115, 101, 32, 116, 104, 101, 32, 96, 98, 97, 99, 107, 119, 97, 114, 100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 96, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 101, 110, 97, 98, 108, 101, 100, 46, 32, 10, 10, 68, 105, 115, 97, 98, 108, 101, 32, 96, 98, 97, 99, 107, 119, 97, 114, 100, 46, 112, 114, 105, 118, 97, 116, 101, 73, 110, 80, 117, 98, 108, 105, 99, 46, 119, 97, 114, 110, 96, 32, 116, 111, 32, 115, 105, 108, 101, 110, 99, 101, 32, 116, 104, 105, 115, 32, 119, 97, 114, 110, 105, 110, 103, 46, 0]};
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 109, 98, 105, 103, 117, 111, 117, 115, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 96, 0]};
static mut l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [96, 59, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 97, 116, 105, 111, 110, 115, 58, 32, 0]};
static mut l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__1_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 0]};
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_realizeGlobalConst___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_realizeGlobalConstCore___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_realizeGlobalConst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_realizeGlobalConst___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [76, 101, 97, 110, 46, 82, 101, 115, 111, 108, 118, 101, 78, 97, 109, 101, 0]};
static mut l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 101, 110, 115, 117, 114, 101, 78, 111, 110, 65, 109, 98, 105, 103, 117, 111, 117, 115, 0]};
static mut l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [97, 109, 98, 105, 103, 117, 111, 117, 115, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32, 96, 0]};
static mut l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [96, 44, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 105, 110, 116, 101, 114, 112, 114, 101, 116, 97, 116, 105, 111, 110, 115, 58, 32, 0]};
static mut l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__1_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__1_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__1_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__3_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__1_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__3_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__3_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__4_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__3_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_executeReservedNameAction___closed__0_value) as *mut crate::leanh::LeanObject,2595672488653442426 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__4_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__4_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__5_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__4_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3834306302553392667 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__5_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__5_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__6_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__5_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,531363388018344998 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__6_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__6_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__7_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__7_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__7_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__8_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__6_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__7_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17717213890053062379 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__8_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__8_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__9_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__9_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__9_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__10_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__8_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__9_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4669553178615429166 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__10_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__10_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__11_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__10_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__2_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10356588175172824407 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__11_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__11_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__11_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_executeReservedNameAction___closed__0_value) as *mut crate::leanh::LeanObject,5193972492090528523 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__0_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_;
    v___x_1778_ = lean_st_mk_ref(v___x_1777_);
    v___x_1779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1779_, 0, v___x_1778_);
    return v___x_1779_;
}
pub unsafe fn l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2____boxed(
    mut v_a_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1781_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_();
    return v_res_1781_;
}
pub unsafe fn _init_l_Lean_registerReservedNameAction___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_registerReservedNameAction___closed__0;
    v___x_1784_ = lean_mk_io_user_error(v___x_1783_);
    return v___x_1784_;
}
pub unsafe fn l_Lean_registerReservedNameAction(
    mut v_act_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut v_a_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1808_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1787_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_1787_) == 0 {
                    v_a_1788_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1804_ = (!crate::leanh::lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1804_ == 0 {
                        v___x_1790_ = v___x_1787_;
                        v_isShared_1791_ = v_isSharedCheck_1804_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1788_);
                        crate::leanh::lean_dec(v___x_1787_);
                        v___x_1790_ = crate::leanh::lean_box(0);
                        v_isShared_1791_ = v_isSharedCheck_1804_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_act_1785_);
                    v_a_1805_ = crate::leanh::lean_ctor_get(v___x_1787_, 0);
                    v_isSharedCheck_1812_ = (!crate::leanh::lean_is_exclusive(v___x_1787_)) as u8;
                    if v_isSharedCheck_1812_ == 0 {
                        v___x_1807_ = v___x_1787_;
                        v_isShared_1808_ = v_isSharedCheck_1812_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1805_);
                        crate::leanh::lean_dec(v___x_1787_);
                        v___x_1807_ = crate::leanh::lean_box(0);
                        v_isShared_1808_ = v_isSharedCheck_1812_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1792_ = (crate::leanh::lean_unbox(v_a_1788_) as u8);
                crate::leanh::lean_dec(v_a_1788_);
                if v___x_1792_ == 0 {
                    crate::leanh::lean_dec_ref(v_act_1785_);
                    v___x_1793_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_registerReservedNameAction___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_registerReservedNameAction___closed__1_once),
                        _init_l_Lean_registerReservedNameAction___closed__1,
                    );
                    if v_isShared_1791_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1790_, 1);
                        crate::leanh::lean_ctor_set(v___x_1790_, 0, v___x_1793_);
                        v___x_1795_ = v___x_1790_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
                        v___x_1795_ = v_reuseFailAlloc_1796_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1797_ =
                        l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
                    v___x_1798_ = lean_st_ref_take(v___x_1797_);
                    v___x_1799_ = lean_array_push(v___x_1798_, v_act_1785_);
                    v___x_1800_ = lean_st_ref_set(v___x_1797_, v___x_1799_);
                    if v_isShared_1791_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1790_, 0, v___x_1800_);
                        v___x_1802_ = v___x_1790_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
                        v___x_1802_ = v_reuseFailAlloc_1803_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1795_;
            }
            3 => {
                return v___x_1802_;
            }
            4 => {
                if v_isShared_1808_ == 0 {
                    v___x_1810_ = v___x_1807_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
                    v___x_1810_ = v_reuseFailAlloc_1811_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerReservedNameAction___boxed(
    mut v_act_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1815_ = l_Lean_registerReservedNameAction(v_act_1813_);
    return v_res_1815_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1817_ = lean_mk_empty_array_with_capacity(v___x_1816_);
    v___x_1818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1818_, 0, v___x_1817_);
    return v___x_1818_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1819_: usize = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1819_ = 5usize;
    v___x_1820_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1821_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1822_ = lean_mk_empty_array_with_capacity(v___x_1821_);
    v___x_1823_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__0);
    v___x_1824_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1824_, 0, v___x_1823_);
    crate::leanh::lean_ctor_set(v___x_1824_, 1, v___x_1822_);
    crate::leanh::lean_ctor_set(v___x_1824_, 2, v___x_1820_);
    crate::leanh::lean_ctor_set(v___x_1824_, 3, v___x_1820_);
    crate::leanh::lean_ctor_set_usize(v___x_1824_, 4, v___x_1819_);
    return v___x_1824_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(
    mut v___y_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v_tid_1843_: u64 = 0;
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1846_: u8 = 0;
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1856_: u8 = 0;
    let mut v_unused_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1827_ = lean_st_ref_get(v___y_1825_);
                v_traceState_1828_ = crate::leanh::lean_ctor_get(v___x_1827_, 4);
                crate::leanh::lean_inc_ref(v_traceState_1828_);
                crate::leanh::lean_dec(v___x_1827_);
                v_traces_1829_ = crate::leanh::lean_ctor_get(v_traceState_1828_, 0);
                crate::leanh::lean_inc_ref(v_traces_1829_);
                crate::leanh::lean_dec_ref(v_traceState_1828_);
                v___x_1830_ = lean_st_ref_take(v___y_1825_);
                v_traceState_1831_ = crate::leanh::lean_ctor_get(v___x_1830_, 4);
                v_env_1832_ = crate::leanh::lean_ctor_get(v___x_1830_, 0);
                v_nextMacroScope_1833_ = crate::leanh::lean_ctor_get(v___x_1830_, 1);
                v_ngen_1834_ = crate::leanh::lean_ctor_get(v___x_1830_, 2);
                v_auxDeclNGen_1835_ = crate::leanh::lean_ctor_get(v___x_1830_, 3);
                v_cache_1836_ = crate::leanh::lean_ctor_get(v___x_1830_, 5);
                v_messages_1837_ = crate::leanh::lean_ctor_get(v___x_1830_, 6);
                v_infoState_1838_ = crate::leanh::lean_ctor_get(v___x_1830_, 7);
                v_snapshotTasks_1839_ = crate::leanh::lean_ctor_get(v___x_1830_, 8);
                v_isSharedCheck_1858_ = (!crate::leanh::lean_is_exclusive(v___x_1830_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v___x_1841_ = v___x_1830_;
                    v_isShared_1842_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1839_);
                    crate::leanh::lean_inc(v_infoState_1838_);
                    crate::leanh::lean_inc(v_messages_1837_);
                    crate::leanh::lean_inc(v_cache_1836_);
                    crate::leanh::lean_inc(v_traceState_1831_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1835_);
                    crate::leanh::lean_inc(v_ngen_1834_);
                    crate::leanh::lean_inc(v_nextMacroScope_1833_);
                    crate::leanh::lean_inc(v_env_1832_);
                    crate::leanh::lean_dec(v___x_1830_);
                    v___x_1841_ = crate::leanh::lean_box(0);
                    v_isShared_1842_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_1843_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1831_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1856_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1831_)) as u8;
                if v_isSharedCheck_1856_ == 0 {
                    v_unused_1857_ = crate::leanh::lean_ctor_get(v_traceState_1831_, 0);
                    crate::leanh::lean_dec(v_unused_1857_);
                    v___x_1845_ = v_traceState_1831_;
                    v_isShared_1846_ = v_isSharedCheck_1856_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_1831_);
                    v___x_1845_ = crate::leanh::lean_box(0);
                    v_isShared_1846_ = v_isSharedCheck_1856_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___closed__1);
                if v_isShared_1846_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1845_, 0, v___x_1847_);
                    v___x_1849_ = v___x_1845_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1855_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1847_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1855_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1843_,
                    );
                    v___x_1849_ = v_reuseFailAlloc_1855_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1842_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1841_, 4, v___x_1849_);
                    v___x_1851_ = v___x_1841_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1854_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_env_1832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_nextMacroScope_1833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_ngen_1834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_auxDeclNGen_1835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 4, v___x_1849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 5, v_cache_1836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 6, v_messages_1837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 7, v_infoState_1838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 8, v_snapshotTasks_1839_);
                    v___x_1851_ = v_reuseFailAlloc_1854_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1852_ = lean_st_ref_set(v___y_1825_, v___x_1851_);
                v___x_1853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1853_, 0, v_traces_1829_);
                return v___x_1853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg___boxed(
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1861_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_1859_);
    crate::leanh::lean_dec(v___y_1859_);
    return v_res_1861_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v___y_1863_);
    return v___x_1865_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___boxed(
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1869_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1(v___y_1866_, v___y_1867_);
    crate::leanh::lean_dec(v___y_1867_);
    crate::leanh::lean_dec_ref(v___y_1866_);
    return v_res_1869_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(
    mut v_opts_1870_: *mut crate::leanh::LeanObject,
    mut v_opt_1871_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1872_ = crate::leanh::lean_ctor_get(v_opt_1871_, 0);
    v_defValue_1873_ = crate::leanh::lean_ctor_get(v_opt_1871_, 1);
    v_map_1874_ = crate::leanh::lean_ctor_get(v_opts_1870_, 0);
    v___x_1875_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1874_,
            v_name_1872_,
        );
    if crate::leanh::lean_obj_tag(v___x_1875_) == 0 {
        let mut v___x_1876_: u8 = 0;
        v___x_1876_ = (crate::leanh::lean_unbox(v_defValue_1873_) as u8);
        return v___x_1876_;
    } else {
        let mut v_val_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1877_ = crate::leanh::lean_ctor_get(v___x_1875_, 0);
        crate::leanh::lean_inc(v_val_1877_);
        crate::leanh::lean_dec_ref_known(v___x_1875_, 1);
        if crate::leanh::lean_obj_tag(v_val_1877_) == 1 {
            let mut v_v_1878_: u8 = 0;
            v_v_1878_ = crate::leanh::lean_ctor_get_uint8(v_val_1877_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1877_, 0);
            return v_v_1878_;
        } else {
            let mut v___x_1879_: u8 = 0;
            crate::leanh::lean_dec(v_val_1877_);
            v___x_1879_ = (crate::leanh::lean_unbox(v_defValue_1873_) as u8);
            return v___x_1879_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2___boxed(
    mut v_opts_1880_: *mut crate::leanh::LeanObject,
    mut v_opt_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1882_: u8 = 0;
    let mut v_r_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1882_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(
        v_opts_1880_,
        v_opt_1881_,
    );
    crate::leanh::lean_dec_ref(v_opt_1881_);
    crate::leanh::lean_dec_ref(v_opts_1880_);
    v_r_1883_ = crate::leanh::lean_box((v_res_1882_) as usize);
    return v_r_1883_;
}
pub unsafe fn _init_l_Lean_executeReservedNameAction___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Lean_executeReservedNameAction___lam__0___closed__0;
    v___x_1886_ = l_Lean_stringToMessageData(v___x_1885_);
    return v___x_1886_;
}
pub unsafe fn l_Lean_executeReservedNameAction___lam__0(
    mut v_name_1887_: *mut crate::leanh::LeanObject,
    mut v_x_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_executeReservedNameAction___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_executeReservedNameAction___lam__0___closed__1_once),
        _init_l_Lean_executeReservedNameAction___lam__0___closed__1,
    );
    v___x_1893_ = l_Lean_MessageData_ofName(v_name_1887_);
    v___x_1894_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1894_, 0, v___x_1892_);
    crate::leanh::lean_ctor_set(v___x_1894_, 1, v___x_1893_);
    v___x_1895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1895_, 0, v___x_1894_);
    return v___x_1895_;
}
pub unsafe fn l_Lean_executeReservedNameAction___lam__0___boxed(
    mut v_name_1896_: *mut crate::leanh::LeanObject,
    mut v_x_1897_: *mut crate::leanh::LeanObject,
    mut v___y_1898_: *mut crate::leanh::LeanObject,
    mut v___y_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_Lean_executeReservedNameAction___lam__0(
        v_name_1896_,
        v_x_1897_,
        v___y_1898_,
        v___y_1899_,
    );
    crate::leanh::lean_dec(v___y_1899_);
    crate::leanh::lean_dec_ref(v___y_1898_);
    crate::leanh::lean_dec_ref(v_x_1897_);
    return v_res_1901_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(
    mut v_opts_1902_: *mut crate::leanh::LeanObject,
    mut v_opt_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1904_ = crate::leanh::lean_ctor_get(v_opt_1903_, 0);
    v_defValue_1905_ = crate::leanh::lean_ctor_get(v_opt_1903_, 1);
    v_map_1906_ = crate::leanh::lean_ctor_get(v_opts_1902_, 0);
    v___x_1907_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1906_,
            v_name_1904_,
        );
    if crate::leanh::lean_obj_tag(v___x_1907_) == 0 {
        crate::leanh::lean_inc(v_defValue_1905_);
        return v_defValue_1905_;
    } else {
        let mut v_val_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1908_ = crate::leanh::lean_ctor_get(v___x_1907_, 0);
        crate::leanh::lean_inc(v_val_1908_);
        crate::leanh::lean_dec_ref_known(v___x_1907_, 1);
        if crate::leanh::lean_obj_tag(v_val_1908_) == 3 {
            let mut v_v_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_1909_ = crate::leanh::lean_ctor_get(v_val_1908_, 0);
            crate::leanh::lean_inc(v_v_1909_);
            crate::leanh::lean_dec_ref_known(v_val_1908_, 1);
            return v_v_1909_;
        } else {
            crate::leanh::lean_dec(v_val_1908_);
            crate::leanh::lean_inc(v_defValue_1905_);
            return v_defValue_1905_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6___boxed(
    mut v_opts_1910_: *mut crate::leanh::LeanObject,
    mut v_opt_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1912_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_1910_, v_opt_1911_);
    crate::leanh::lean_dec_ref(v_opt_1911_);
    crate::leanh::lean_dec_ref(v_opts_1910_);
    return v_res_1912_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(
    mut v_e_1913_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_1913_) == 0 {
        let mut v___x_1914_: u8 = 0;
        v___x_1914_ = 2;
        return v___x_1914_;
    } else {
        let mut v_a_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1916_: u8 = 0;
        v_a_1915_ = crate::leanh::lean_ctor_get(v_e_1913_, 0);
        v___x_1916_ = (crate::leanh::lean_unbox(v_a_1915_) as u8);
        if v___x_1916_ == 0 {
            let mut v___x_1917_: u8 = 0;
            v___x_1917_ = 1;
            return v___x_1917_;
        } else {
            let mut v___x_1918_: u8 = 0;
            v___x_1918_ = 0;
            return v___x_1918_;
        }
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3___boxed(
    mut v_e_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1920_: u8 = 0;
    let mut v_r_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_e_1919_);
    crate::leanh::lean_dec_ref(v_e_1919_);
    v_r_1921_ = crate::leanh::lean_box((v_res_1920_) as usize);
    return v_r_1921_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1922_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1922_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__0);
    v___x_1924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1924_, 0, v___x_1923_);
    return v___x_1924_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1);
    v___x_1926_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1927_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1927_, 0, v___x_1926_);
    crate::leanh::lean_ctor_set(v___x_1927_, 1, v___x_1926_);
    crate::leanh::lean_ctor_set(v___x_1927_, 2, v___x_1926_);
    crate::leanh::lean_ctor_set(v___x_1927_, 3, v___x_1926_);
    crate::leanh::lean_ctor_set(v___x_1927_, 4, v___x_1925_);
    crate::leanh::lean_ctor_set(v___x_1927_, 5, v___x_1925_);
    crate::leanh::lean_ctor_set(v___x_1927_, 6, v___x_1925_);
    crate::leanh::lean_ctor_set(v___x_1927_, 7, v___x_1925_);
    crate::leanh::lean_ctor_set(v___x_1927_, 8, v___x_1925_);
    crate::leanh::lean_ctor_set(v___x_1927_, 9, v___x_1925_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1929_ = lean_mk_empty_array_with_capacity(v___x_1928_);
    v___x_1930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1930_, 0, v___x_1929_);
    return v___x_1930_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: usize = 0;
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = 5usize;
    v___x_1932_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1933_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1934_ = lean_mk_empty_array_with_capacity(v___x_1933_);
    v___x_1935_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__3);
    v___x_1936_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_1935_);
    crate::leanh::lean_ctor_set(v___x_1936_, 1, v___x_1934_);
    crate::leanh::lean_ctor_set(v___x_1936_, 2, v___x_1932_);
    crate::leanh::lean_ctor_set(v___x_1936_, 3, v___x_1932_);
    crate::leanh::lean_ctor_set_usize(v___x_1936_, 4, v___x_1931_);
    return v___x_1936_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1937_ = crate::leanh::lean_box(1);
    v___x_1938_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__4);
    v___x_1939_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__1);
    v___x_1940_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1940_, 0, v___x_1939_);
    crate::leanh::lean_ctor_set(v___x_1940_, 1, v___x_1938_);
    crate::leanh::lean_ctor_set(v___x_1940_, 2, v___x_1937_);
    return v___x_1940_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(
    mut v_msgData_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
    mut v___y_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = lean_st_ref_get(v___y_1943_);
    v_env_1946_ = crate::leanh::lean_ctor_get(v___x_1945_, 0);
    crate::leanh::lean_inc_ref(v_env_1946_);
    crate::leanh::lean_dec(v___x_1945_);
    v_options_1947_ = crate::leanh::lean_ctor_get(v___y_1942_, 2);
    v___x_1948_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2);
    v___x_1949_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5);
    crate::leanh::lean_inc_ref(v_options_1947_);
    v___x_1950_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1950_, 0, v_env_1946_);
    crate::leanh::lean_ctor_set(v___x_1950_, 1, v___x_1948_);
    crate::leanh::lean_ctor_set(v___x_1950_, 2, v___x_1949_);
    crate::leanh::lean_ctor_set(v___x_1950_, 3, v_options_1947_);
    v___x_1951_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1951_, 0, v___x_1950_);
    crate::leanh::lean_ctor_set(v___x_1951_, 1, v_msgData_1941_);
    v___x_1952_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1952_, 0, v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___boxed(
    mut v_msgData_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(v_msgData_1953_, v___y_1954_, v___y_1955_);
    crate::leanh::lean_dec(v___y_1955_);
    crate::leanh::lean_dec_ref(v___y_1954_);
    return v_res_1957_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5(
    mut v_sz_1958_: usize,
    mut v_i_1959_: usize,
    mut v_bs_1960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1961_: u8 = 0;
    let mut v_v_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: usize = 0;
    let mut v___x_1967_: usize = 0;
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1961_ = lean_usize_dec_lt(v_i_1959_, v_sz_1958_);
                if v___x_1961_ == 0 {
                    return v_bs_1960_;
                } else {
                    v_v_1962_ = lean_array_uget_borrowed(v_bs_1960_, v_i_1959_);
                    v_msg_1963_ = crate::leanh::lean_ctor_get(v_v_1962_, 1);
                    crate::leanh::lean_inc_ref(v_msg_1963_);
                    v___x_1964_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1965_ = lean_array_uset(v_bs_1960_, v_i_1959_, v___x_1964_);
                    v___x_1966_ = 1usize;
                    v___x_1967_ = lean_usize_add(v_i_1959_, v___x_1966_);
                    v___x_1968_ = lean_array_uset(v_bs_x27_1965_, v_i_1959_, v_msg_1963_);
                    v_i_1959_ = v___x_1967_;
                    v_bs_1960_ = v___x_1968_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5___boxed(
    mut v_sz_1970_: *mut crate::leanh::LeanObject,
    mut v_i_1971_: *mut crate::leanh::LeanObject,
    mut v_bs_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1973_: usize = 0;
    let mut v_i_boxed_1974_: usize = 0;
    let mut v_res_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1973_ = crate::leanh::lean_unbox_usize(v_sz_1970_);
    crate::leanh::lean_dec(v_sz_1970_);
    v_i_boxed_1974_ = crate::leanh::lean_unbox_usize(v_i_1971_);
    crate::leanh::lean_dec(v_i_1971_);
    v_res_1975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5(v_sz_boxed_1973_, v_i_boxed_1974_, v_bs_1972_);
    return v_res_1975_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(
    mut v_oldTraces_1976_: *mut crate::leanh::LeanObject,
    mut v_data_1977_: *mut crate::leanh::LeanObject,
    mut v_ref_1978_: *mut crate::leanh::LeanObject,
    mut v_msg_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1995_: u8 = 0;
    let mut v_cancelTk_x3f_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1997_: u8 = 0;
    let mut v_inheritedTraceOptions_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2005_: usize = 0;
    let mut v___x_2006_: usize = 0;
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v_tid_2027_: u64 = 0;
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2030_: u8 = 0;
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut v_unused_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_isSharedCheck_2047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1983_ = crate::leanh::lean_ctor_get(v___y_1980_, 0);
                v_fileMap_1984_ = crate::leanh::lean_ctor_get(v___y_1980_, 1);
                v_options_1985_ = crate::leanh::lean_ctor_get(v___y_1980_, 2);
                v_currRecDepth_1986_ = crate::leanh::lean_ctor_get(v___y_1980_, 3);
                v_maxRecDepth_1987_ = crate::leanh::lean_ctor_get(v___y_1980_, 4);
                v_ref_1988_ = crate::leanh::lean_ctor_get(v___y_1980_, 5);
                v_currNamespace_1989_ = crate::leanh::lean_ctor_get(v___y_1980_, 6);
                v_openDecls_1990_ = crate::leanh::lean_ctor_get(v___y_1980_, 7);
                v_initHeartbeats_1991_ = crate::leanh::lean_ctor_get(v___y_1980_, 8);
                v_maxHeartbeats_1992_ = crate::leanh::lean_ctor_get(v___y_1980_, 9);
                v_quotContext_1993_ = crate::leanh::lean_ctor_get(v___y_1980_, 10);
                v_currMacroScope_1994_ = crate::leanh::lean_ctor_get(v___y_1980_, 11);
                v_diag_1995_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1980_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1996_ = crate::leanh::lean_ctor_get(v___y_1980_, 12);
                v_suppressElabErrors_1997_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1980_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1998_ = crate::leanh::lean_ctor_get(v___y_1980_, 13);
                v___x_1999_ = lean_st_ref_get(v___y_1981_);
                v_traceState_2000_ = crate::leanh::lean_ctor_get(v___x_1999_, 4);
                crate::leanh::lean_inc_ref(v_traceState_2000_);
                crate::leanh::lean_dec(v___x_1999_);
                v_traces_2001_ = crate::leanh::lean_ctor_get(v_traceState_2000_, 0);
                crate::leanh::lean_inc_ref(v_traces_2001_);
                crate::leanh::lean_dec_ref(v_traceState_2000_);
                v_ref_2002_ = l_Lean_replaceRef(v_ref_1978_, v_ref_1988_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1998_);
                crate::leanh::lean_inc(v_cancelTk_x3f_1996_);
                crate::leanh::lean_inc(v_currMacroScope_1994_);
                crate::leanh::lean_inc(v_quotContext_1993_);
                crate::leanh::lean_inc(v_maxHeartbeats_1992_);
                crate::leanh::lean_inc(v_initHeartbeats_1991_);
                crate::leanh::lean_inc(v_openDecls_1990_);
                crate::leanh::lean_inc(v_currNamespace_1989_);
                crate::leanh::lean_inc(v_maxRecDepth_1987_);
                crate::leanh::lean_inc(v_currRecDepth_1986_);
                crate::leanh::lean_inc_ref(v_options_1985_);
                crate::leanh::lean_inc_ref(v_fileMap_1984_);
                crate::leanh::lean_inc_ref(v_fileName_1983_);
                v___x_2003_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2003_, 0, v_fileName_1983_);
                crate::leanh::lean_ctor_set(v___x_2003_, 1, v_fileMap_1984_);
                crate::leanh::lean_ctor_set(v___x_2003_, 2, v_options_1985_);
                crate::leanh::lean_ctor_set(v___x_2003_, 3, v_currRecDepth_1986_);
                crate::leanh::lean_ctor_set(v___x_2003_, 4, v_maxRecDepth_1987_);
                crate::leanh::lean_ctor_set(v___x_2003_, 5, v_ref_2002_);
                crate::leanh::lean_ctor_set(v___x_2003_, 6, v_currNamespace_1989_);
                crate::leanh::lean_ctor_set(v___x_2003_, 7, v_openDecls_1990_);
                crate::leanh::lean_ctor_set(v___x_2003_, 8, v_initHeartbeats_1991_);
                crate::leanh::lean_ctor_set(v___x_2003_, 9, v_maxHeartbeats_1992_);
                crate::leanh::lean_ctor_set(v___x_2003_, 10, v_quotContext_1993_);
                crate::leanh::lean_ctor_set(v___x_2003_, 11, v_currMacroScope_1994_);
                crate::leanh::lean_ctor_set(v___x_2003_, 12, v_cancelTk_x3f_1996_);
                crate::leanh::lean_ctor_set(v___x_2003_, 13, v_inheritedTraceOptions_1998_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2003_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_1995_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2003_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1997_,
                );
                v___x_2004_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2001_);
                crate::leanh::lean_dec_ref(v_traces_2001_);
                v_sz_2005_ = lean_array_size(v___x_2004_);
                v___x_2006_ = 0usize;
                v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__5(v_sz_2005_, v___x_2006_, v___x_2004_);
                v_msg_2008_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_2008_, 0, v_data_1977_);
                crate::leanh::lean_ctor_set(v_msg_2008_, 1, v_msg_1979_);
                crate::leanh::lean_ctor_set(v_msg_2008_, 2, v___x_2007_);
                v___x_2009_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(v_msg_2008_, v___x_2003_, v___y_1981_);
                crate::leanh::lean_dec_ref_known(v___x_2003_, 14);
                v_a_2010_ = crate::leanh::lean_ctor_get(v___x_2009_, 0);
                v_isSharedCheck_2047_ = (!crate::leanh::lean_is_exclusive(v___x_2009_)) as u8;
                if v_isSharedCheck_2047_ == 0 {
                    v___x_2012_ = v___x_2009_;
                    v_isShared_2013_ = v_isSharedCheck_2047_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2010_);
                    crate::leanh::lean_dec(v___x_2009_);
                    v___x_2012_ = crate::leanh::lean_box(0);
                    v_isShared_2013_ = v_isSharedCheck_2047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2014_ = lean_st_ref_take(v___y_1981_);
                v_traceState_2015_ = crate::leanh::lean_ctor_get(v___x_2014_, 4);
                v_env_2016_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
                v_nextMacroScope_2017_ = crate::leanh::lean_ctor_get(v___x_2014_, 1);
                v_ngen_2018_ = crate::leanh::lean_ctor_get(v___x_2014_, 2);
                v_auxDeclNGen_2019_ = crate::leanh::lean_ctor_get(v___x_2014_, 3);
                v_cache_2020_ = crate::leanh::lean_ctor_get(v___x_2014_, 5);
                v_messages_2021_ = crate::leanh::lean_ctor_get(v___x_2014_, 6);
                v_infoState_2022_ = crate::leanh::lean_ctor_get(v___x_2014_, 7);
                v_snapshotTasks_2023_ = crate::leanh::lean_ctor_get(v___x_2014_, 8);
                v_isSharedCheck_2046_ = (!crate::leanh::lean_is_exclusive(v___x_2014_)) as u8;
                if v_isSharedCheck_2046_ == 0 {
                    v___x_2025_ = v___x_2014_;
                    v_isShared_2026_ = v_isSharedCheck_2046_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2023_);
                    crate::leanh::lean_inc(v_infoState_2022_);
                    crate::leanh::lean_inc(v_messages_2021_);
                    crate::leanh::lean_inc(v_cache_2020_);
                    crate::leanh::lean_inc(v_traceState_2015_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2019_);
                    crate::leanh::lean_inc(v_ngen_2018_);
                    crate::leanh::lean_inc(v_nextMacroScope_2017_);
                    crate::leanh::lean_inc(v_env_2016_);
                    crate::leanh::lean_dec(v___x_2014_);
                    v___x_2025_ = crate::leanh::lean_box(0);
                    v_isShared_2026_ = v_isSharedCheck_2046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2027_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2015_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2044_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2015_)) as u8;
                if v_isSharedCheck_2044_ == 0 {
                    v_unused_2045_ = crate::leanh::lean_ctor_get(v_traceState_2015_, 0);
                    crate::leanh::lean_dec(v_unused_2045_);
                    v___x_2029_ = v_traceState_2015_;
                    v_isShared_2030_ = v_isSharedCheck_2044_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_2015_);
                    v___x_2029_ = crate::leanh::lean_box(0);
                    v_isShared_2030_ = v_isSharedCheck_2044_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2031_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2031_, 0, v_ref_1978_);
                crate::leanh::lean_ctor_set(v___x_2031_, 1, v_a_2010_);
                v___x_2032_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1976_, v___x_2031_);
                if v_isShared_2030_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2029_, 0, v___x_2032_);
                    v___x_2034_ = v___x_2029_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2043_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2032_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2027_,
                    );
                    v___x_2034_ = v_reuseFailAlloc_2043_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2025_, 4, v___x_2034_);
                    v___x_2036_ = v___x_2025_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_env_2016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_nextMacroScope_2017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 2, v_ngen_2018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 3, v_auxDeclNGen_2019_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 4, v___x_2034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 5, v_cache_2020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 6, v_messages_2021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 7, v_infoState_2022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 8, v_snapshotTasks_2023_);
                    v___x_2036_ = v_reuseFailAlloc_2042_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2037_ = lean_st_ref_set(v___y_1981_, v___x_2036_);
                v___x_2038_ = crate::leanh::lean_box(0);
                if v_isShared_2013_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2012_, 0, v___x_2038_);
                    v___x_2040_ = v___x_2012_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
                    v___x_2040_ = v_reuseFailAlloc_2041_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4___boxed(
    mut v_oldTraces_2048_: *mut crate::leanh::LeanObject,
    mut v_data_2049_: *mut crate::leanh::LeanObject,
    mut v_ref_2050_: *mut crate::leanh::LeanObject,
    mut v_msg_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
    mut v___y_2054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2055_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_oldTraces_2048_, v_data_2049_, v_ref_2050_, v_msg_2051_, v___y_2052_, v___y_2053_);
    crate::leanh::lean_dec(v___y_2053_);
    crate::leanh::lean_dec_ref(v___y_2052_);
    return v_res_2055_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(
    mut v_x_2056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2061_: u8 = 0;
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2065_: u8 = 0;
    let mut v_a_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2056_) == 0 {
                    v_a_2058_ = crate::leanh::lean_ctor_get(v_x_2056_, 0);
                    v_isSharedCheck_2065_ = (!crate::leanh::lean_is_exclusive(v_x_2056_)) as u8;
                    if v_isSharedCheck_2065_ == 0 {
                        v___x_2060_ = v_x_2056_;
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2058_);
                        crate::leanh::lean_dec(v_x_2056_);
                        v___x_2060_ = crate::leanh::lean_box(0);
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2066_ = crate::leanh::lean_ctor_get(v_x_2056_, 0);
                    v_isSharedCheck_2073_ = (!crate::leanh::lean_is_exclusive(v_x_2056_)) as u8;
                    if v_isSharedCheck_2073_ == 0 {
                        v___x_2068_ = v_x_2056_;
                        v_isShared_2069_ = v_isSharedCheck_2073_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2066_);
                        crate::leanh::lean_dec(v_x_2056_);
                        v___x_2068_ = crate::leanh::lean_box(0);
                        v_isShared_2069_ = v_isSharedCheck_2073_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2061_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2060_, 1);
                    v___x_2063_ = v___x_2060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
                    v___x_2063_ = v_reuseFailAlloc_2064_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2063_;
            }
            3 => {
                if v_isShared_2069_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2068_, 0);
                    v___x_2071_ = v___x_2068_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
                    v___x_2071_ = v_reuseFailAlloc_2072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg___boxed(
    mut v_x_2074_: *mut crate::leanh::LeanObject,
    mut v___y_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2076_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(v_x_2074_);
    return v_res_2076_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2078_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__0;
    v___x_2079_ = l_Lean_stringToMessageData(v___x_2078_);
    return v___x_2079_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2()
-> f64 {
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: f64 = 0.0;
    v___x_2080_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2081_ = lean_float_of_nat(v___x_2080_);
    return v___x_2081_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__3;
    v___x_2084_ = l_Lean_stringToMessageData(v___x_2083_);
    return v___x_2084_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5()
-> f64 {
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: f64 = 0.0;
    v___x_2085_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_2086_ = lean_float_of_nat(v___x_2085_);
    return v___x_2086_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(
    mut v_cls_2087_: *mut crate::leanh::LeanObject,
    mut v_collapsed_2088_: u8,
    mut v_tag_2089_: *mut crate::leanh::LeanObject,
    mut v_opts_2090_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_2091_: u8,
    mut v_oldTraces_2092_: *mut crate::leanh::LeanObject,
    mut v_msg_2093_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2102_: u8 = 0;
    let mut v___y_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut v_fst_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: u8 = 0;
    let mut v___y_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2127_: u8 = 0;
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: f64 = 0.0;
    let mut v_data_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: f64 = 0.0;
    let mut v___x_2141_: f64 = 0.0;
    let mut v_reuseFailAlloc_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2150_: u8 = 0;
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v_tid_2164_: u64 = 0;
    let mut v_traces_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v___y_2181_: f64 = 0.0;
    let mut v___x_2182_: f64 = 0.0;
    let mut v___x_2183_: f64 = 0.0;
    let mut v___x_2184_: f64 = 0.0;
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: f64 = 0.0;
    let mut v___x_2191_: f64 = 0.0;
    let mut v___x_2192_: f64 = 0.0;
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: f64 = 0.0;
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2098_ = crate::leanh::lean_ctor_get(v_resStartStop_2094_, 0);
                v_snd_2099_ = crate::leanh::lean_ctor_get(v_resStartStop_2094_, 1);
                v_isSharedCheck_2197_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_2094_)) as u8;
                if v_isSharedCheck_2197_ == 0 {
                    v___x_2101_ = v_resStartStop_2094_;
                    v_isShared_2102_ = v_isSharedCheck_2197_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2099_);
                    crate::leanh::lean_inc(v_fst_2098_);
                    crate::leanh::lean_dec(v_resStartStop_2094_);
                    v___x_2101_ = crate::leanh::lean_box(0);
                    v_isShared_2102_ = v_isSharedCheck_2197_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2117_ = crate::leanh::lean_ctor_get(v_snd_2099_, 0);
                v_snd_2118_ = crate::leanh::lean_ctor_get(v_snd_2099_, 1);
                v_isSharedCheck_2196_ = (!crate::leanh::lean_is_exclusive(v_snd_2099_)) as u8;
                if v_isSharedCheck_2196_ == 0 {
                    v___x_2120_ = v_snd_2099_;
                    v_isShared_2121_ = v_isSharedCheck_2196_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2118_);
                    crate::leanh::lean_inc(v_fst_2117_);
                    crate::leanh::lean_dec(v_snd_2099_);
                    v___x_2120_ = crate::leanh::lean_box(0);
                    v_isShared_2121_ = v_isSharedCheck_2196_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_2105_);
                v___x_2107_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4(v_oldTraces_2092_, v_data_2106_, v___y_2105_, v___y_2104_, v___y_2095_, v___y_2096_);
                if crate::leanh::lean_obj_tag(v___x_2107_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2107_, 1);
                    v___x_2108_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(v_fst_2098_);
                    return v___x_2108_;
                } else {
                    crate::leanh::lean_dec(v_fst_2098_);
                    v_a_2109_ = crate::leanh::lean_ctor_get(v___x_2107_, 0);
                    v_isSharedCheck_2116_ = (!crate::leanh::lean_is_exclusive(v___x_2107_)) as u8;
                    if v_isSharedCheck_2116_ == 0 {
                        v___x_2111_ = v___x_2107_;
                        v_isShared_2112_ = v_isSharedCheck_2116_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2109_);
                        crate::leanh::lean_dec(v___x_2107_);
                        v___x_2111_ = crate::leanh::lean_box(0);
                        v_isShared_2112_ = v_isSharedCheck_2116_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2112_ == 0 {
                    v___x_2114_ = v___x_2111_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
                    v___x_2114_ = v_reuseFailAlloc_2115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2114_;
            }
            5 => {
                v___x_2122_ = l_Lean_trace_profiler;
                v___x_2123_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(
                    v_opts_2090_,
                    v___x_2122_,
                );
                if v___x_2123_ == 0 {
                    v___y_2150_ = v___x_2123_;
                    state = 10;
                    continue;
                } else {
                    v___x_2186_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_2187_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(
                        v_opts_2090_,
                        v___x_2186_,
                    );
                    if v___x_2187_ == 0 {
                        v___x_2188_ = l_Lean_trace_profiler_threshold;
                        v___x_2189_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_2090_, v___x_2188_);
                        v___x_2190_ = lean_float_of_nat(v___x_2189_);
                        v___x_2191_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__5);
                        v___x_2192_ = lean_float_div(v___x_2190_, v___x_2191_);
                        v___y_2181_ = v___x_2192_;
                        state = 15;
                        continue;
                    } else {
                        v___x_2193_ = l_Lean_trace_profiler_threshold;
                        v___x_2194_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__6(v_opts_2090_, v___x_2193_);
                        v___x_2195_ = lean_float_of_nat(v___x_2194_);
                        v___y_2181_ = v___x_2195_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_2127_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__3(v_fst_2098_);
                v___x_2128_ = l_Lean_TraceResult_toEmoji(v_result_2127_);
                v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
                v___x_2130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__1);
                if v_isShared_2121_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2120_, 7);
                    crate::leanh::lean_ctor_set(v___x_2120_, 1, v___x_2130_);
                    crate::leanh::lean_ctor_set(v___x_2120_, 0, v___x_2129_);
                    v___x_2132_ = v___x_2120_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2143_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2129_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2130_);
                    v___x_2132_ = v_reuseFailAlloc_2143_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2102_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2101_, 7);
                    crate::leanh::lean_ctor_set(v___x_2101_, 1, v_a_2126_);
                    crate::leanh::lean_ctor_set(v___x_2101_, 0, v___x_2132_);
                    v_m_2134_ = v___x_2101_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2132_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_a_2126_);
                    v_m_2134_ = v_reuseFailAlloc_2142_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2135_ = crate::leanh::lean_box((v_result_2127_) as usize);
                v___x_2136_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2135_);
                v___x_2137_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__2);
                crate::leanh::lean_inc_ref(v_tag_2089_);
                crate::leanh::lean_inc_ref(v___x_2136_);
                crate::leanh::lean_inc(v_cls_2087_);
                v_data_2138_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_2138_, 0, v_cls_2087_);
                crate::leanh::lean_ctor_set(v_data_2138_, 1, v___x_2136_);
                crate::leanh::lean_ctor_set(v_data_2138_, 2, v_tag_2089_);
                crate::leanh::lean_ctor_set_float(
                    v_data_2138_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2137_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_2138_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2137_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_2138_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_2088_,
                );
                if v___x_2123_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2136_, 1);
                    crate::leanh::lean_dec(v_snd_2118_);
                    crate::leanh::lean_dec(v_fst_2117_);
                    crate::leanh::lean_dec_ref(v_tag_2089_);
                    crate::leanh::lean_dec(v_cls_2087_);
                    v___y_2104_ = v_m_2134_;
                    v___y_2105_ = v___y_2125_;
                    v_data_2106_ = v_data_2138_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_2138_, 3);
                    v_data_2139_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_2139_, 0, v_cls_2087_);
                    crate::leanh::lean_ctor_set(v_data_2139_, 1, v___x_2136_);
                    crate::leanh::lean_ctor_set(v_data_2139_, 2, v_tag_2089_);
                    v___x_2140_ = crate::leanh::lean_unbox_float(v_fst_2117_);
                    crate::leanh::lean_dec(v_fst_2117_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_2139_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_2140_,
                    );
                    v___x_2141_ = crate::leanh::lean_unbox_float(v_snd_2118_);
                    crate::leanh::lean_dec(v_snd_2118_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_2139_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_2141_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_2139_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_2088_,
                    );
                    v___y_2104_ = v_m_2134_;
                    v___y_2105_ = v___y_2125_;
                    v_data_2106_ = v_data_2139_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_2145_ = crate::leanh::lean_ctor_get(v___y_2095_, 5);
                crate::leanh::lean_inc(v___y_2096_);
                crate::leanh::lean_inc_ref(v___y_2095_);
                crate::leanh::lean_inc(v_fst_2098_);
                v___x_2146_ = crate::leanh::lean_apply_4(
                    v_msg_2093_,
                    v_fst_2098_,
                    v___y_2095_,
                    v___y_2096_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2146_) == 0 {
                    v_a_2147_ = crate::leanh::lean_ctor_get(v___x_2146_, 0);
                    crate::leanh::lean_inc(v_a_2147_);
                    crate::leanh::lean_dec_ref_known(v___x_2146_, 1);
                    v___y_2125_ = v_ref_2145_;
                    v_a_2126_ = v_a_2147_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2146_, 1);
                    v___x_2148_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___closed__4);
                    v___y_2125_ = v_ref_2145_;
                    v_a_2126_ = v___x_2148_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_2091_ == 0 {
                    if v___y_2150_ == 0 {
                        crate::leanh::lean_del_object(v___x_2120_);
                        crate::leanh::lean_dec(v_snd_2118_);
                        crate::leanh::lean_dec(v_fst_2117_);
                        crate::leanh::lean_del_object(v___x_2101_);
                        crate::leanh::lean_dec_ref(v_msg_2093_);
                        crate::leanh::lean_dec_ref(v_tag_2089_);
                        crate::leanh::lean_dec(v_cls_2087_);
                        v___x_2151_ = lean_st_ref_take(v___y_2096_);
                        v_traceState_2152_ = crate::leanh::lean_ctor_get(v___x_2151_, 4);
                        v_env_2153_ = crate::leanh::lean_ctor_get(v___x_2151_, 0);
                        v_nextMacroScope_2154_ = crate::leanh::lean_ctor_get(v___x_2151_, 1);
                        v_ngen_2155_ = crate::leanh::lean_ctor_get(v___x_2151_, 2);
                        v_auxDeclNGen_2156_ = crate::leanh::lean_ctor_get(v___x_2151_, 3);
                        v_cache_2157_ = crate::leanh::lean_ctor_get(v___x_2151_, 5);
                        v_messages_2158_ = crate::leanh::lean_ctor_get(v___x_2151_, 6);
                        v_infoState_2159_ = crate::leanh::lean_ctor_get(v___x_2151_, 7);
                        v_snapshotTasks_2160_ = crate::leanh::lean_ctor_get(v___x_2151_, 8);
                        v_isSharedCheck_2179_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2151_)) as u8;
                        if v_isSharedCheck_2179_ == 0 {
                            v___x_2162_ = v___x_2151_;
                            v_isShared_2163_ = v_isSharedCheck_2179_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_2160_);
                            crate::leanh::lean_inc(v_infoState_2159_);
                            crate::leanh::lean_inc(v_messages_2158_);
                            crate::leanh::lean_inc(v_cache_2157_);
                            crate::leanh::lean_inc(v_traceState_2152_);
                            crate::leanh::lean_inc(v_auxDeclNGen_2156_);
                            crate::leanh::lean_inc(v_ngen_2155_);
                            crate::leanh::lean_inc(v_nextMacroScope_2154_);
                            crate::leanh::lean_inc(v_env_2153_);
                            crate::leanh::lean_dec(v___x_2151_);
                            v___x_2162_ = crate::leanh::lean_box(0);
                            v_isShared_2163_ = v_isSharedCheck_2179_;
                            state = 11;
                            continue;
                        }
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_tid_2164_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2152_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2165_ = crate::leanh::lean_ctor_get(v_traceState_2152_, 0);
                v_isSharedCheck_2178_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2152_)) as u8;
                if v_isSharedCheck_2178_ == 0 {
                    v___x_2167_ = v_traceState_2152_;
                    v_isShared_2168_ = v_isSharedCheck_2178_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2165_);
                    crate::leanh::lean_dec(v_traceState_2152_);
                    v___x_2167_ = crate::leanh::lean_box(0);
                    v_isShared_2168_ = v_isSharedCheck_2178_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2169_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_2092_, v_traces_2165_);
                crate::leanh::lean_dec_ref(v_traces_2165_);
                if v_isShared_2168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2167_, 0, v___x_2169_);
                    v___x_2171_ = v___x_2167_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2169_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2177_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2164_,
                    );
                    v___x_2171_ = v_reuseFailAlloc_2177_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2162_, 4, v___x_2171_);
                    v___x_2173_ = v___x_2162_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2176_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_env_2153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_nextMacroScope_2154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_ngen_2155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_auxDeclNGen_2156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 4, v___x_2171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 5, v_cache_2157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 6, v_messages_2158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 7, v_infoState_2159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 8, v_snapshotTasks_2160_);
                    v___x_2173_ = v_reuseFailAlloc_2176_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2174_ = lean_st_ref_set(v___y_2096_, v___x_2173_);
                v___x_2175_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(v_fst_2098_);
                return v___x_2175_;
            }
            15 => {
                v___x_2182_ = crate::leanh::lean_unbox_float(v_snd_2118_);
                v___x_2183_ = crate::leanh::lean_unbox_float(v_fst_2117_);
                v___x_2184_ = lean_float_sub(v___x_2182_, v___x_2183_);
                v___x_2185_ = lean_float_decLt(v___y_2181_, v___x_2184_);
                v___y_2150_ = v___x_2185_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3___boxed(
    mut v_cls_2198_: *mut crate::leanh::LeanObject,
    mut v_collapsed_2199_: *mut crate::leanh::LeanObject,
    mut v_tag_2200_: *mut crate::leanh::LeanObject,
    mut v_opts_2201_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_2202_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_2203_: *mut crate::leanh::LeanObject,
    mut v_msg_2204_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v___y_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_2209_: u8 = 0;
    let mut v_clsEnabled_boxed_2210_: u8 = 0;
    let mut v_res_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_2209_ = (crate::leanh::lean_unbox(v_collapsed_2199_) as u8);
    v_clsEnabled_boxed_2210_ = (crate::leanh::lean_unbox(v_clsEnabled_2202_) as u8);
    v_res_2211_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v_cls_2198_, v_collapsed_boxed_2209_, v_tag_2200_, v_opts_2201_, v_clsEnabled_boxed_2210_, v_oldTraces_2203_, v_msg_2204_, v_resStartStop_2205_, v___y_2206_, v___y_2207_);
    crate::leanh::lean_dec(v___y_2207_);
    crate::leanh::lean_dec_ref(v___y_2206_);
    crate::leanh::lean_dec_ref(v_opts_2201_);
    return v_res_2211_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(
    mut v_name_2212_: *mut crate::leanh::LeanObject,
    mut v_as_2213_: *mut crate::leanh::LeanObject,
    mut v_i_2214_: usize,
    mut v_stop_2215_: usize,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2219_: u8 = 0;
    let mut v___x_5305__overap_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: usize = 0;
    let mut v___x_2228_: usize = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2219_ = lean_usize_dec_eq(v_i_2214_, v_stop_2215_);
                if v___x_2219_ == 0 {
                    v___x_5305__overap_2220_ = lean_array_uget_borrowed(v_as_2213_, v_i_2214_);
                    crate::leanh::lean_inc(v___x_5305__overap_2220_);
                    crate::leanh::lean_inc(v___y_2217_);
                    crate::leanh::lean_inc_ref(v___y_2216_);
                    crate::leanh::lean_inc(v_name_2212_);
                    v___x_2221_ = crate::leanh::lean_apply_4(
                        v___x_5305__overap_2220_,
                        v_name_2212_,
                        v___y_2216_,
                        v___y_2217_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2221_) == 0 {
                        v_a_2222_ = crate::leanh::lean_ctor_get(v___x_2221_, 0);
                        v_isSharedCheck_2233_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2221_)) as u8;
                        if v_isSharedCheck_2233_ == 0 {
                            v___x_2224_ = v___x_2221_;
                            v_isShared_2225_ = v_isSharedCheck_2233_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2222_);
                            crate::leanh::lean_dec(v___x_2221_);
                            v___x_2224_ = crate::leanh::lean_box(0);
                            v_isShared_2225_ = v_isSharedCheck_2233_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_name_2212_);
                        return v___x_2221_;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_2212_);
                    v___x_2234_ = 0;
                    v___x_2235_ = crate::leanh::lean_box((v___x_2234_) as usize);
                    v___x_2236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2236_, 0, v___x_2235_);
                    return v___x_2236_;
                }
            }
            1 => {
                v___x_2226_ = (crate::leanh::lean_unbox(v_a_2222_) as u8);
                if v___x_2226_ == 0 {
                    crate::leanh::lean_del_object(v___x_2224_);
                    crate::leanh::lean_dec(v_a_2222_);
                    v___x_2227_ = 1usize;
                    v___x_2228_ = lean_usize_add(v_i_2214_, v___x_2227_);
                    v_i_2214_ = v___x_2228_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_name_2212_);
                    if v_isShared_2225_ == 0 {
                        v___x_2231_ = v___x_2224_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2222_);
                        v___x_2231_ = v_reuseFailAlloc_2232_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0___boxed(
    mut v_name_2237_: *mut crate::leanh::LeanObject,
    mut v_as_2238_: *mut crate::leanh::LeanObject,
    mut v_i_2239_: *mut crate::leanh::LeanObject,
    mut v_stop_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2244_: usize = 0;
    let mut v_stop_boxed_2245_: usize = 0;
    let mut v_res_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2244_ = crate::leanh::lean_unbox_usize(v_i_2239_);
    crate::leanh::lean_dec(v_i_2239_);
    v_stop_boxed_2245_ = crate::leanh::lean_unbox_usize(v_stop_2240_);
    crate::leanh::lean_dec(v_stop_2240_);
    v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_2237_, v_as_2238_, v_i_boxed_2244_, v_stop_boxed_2245_, v___y_2241_, v___y_2242_);
    crate::leanh::lean_dec(v___y_2242_);
    crate::leanh::lean_dec_ref(v___y_2241_);
    crate::leanh::lean_dec_ref(v_as_2238_);
    return v_res_2246_;
}
pub unsafe fn _init_l_Lean_executeReservedNameAction___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ = l_Lean_executeReservedNameAction___closed__1;
    v___x_2255_ = l_Lean_executeReservedNameAction___closed__4;
    v___x_2256_ = l_Lean_Name_append(v___x_2255_, v___x_2254_);
    return v___x_2256_;
}
pub unsafe fn _init_l_Lean_executeReservedNameAction___closed__6() -> f64 {
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: f64 = 0.0;
    v___x_2257_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_2258_ = lean_float_of_nat(v___x_2257_);
    return v___x_2258_;
}
pub unsafe fn l_Lean_executeReservedNameAction(
    mut v_name_2259_: *mut crate::leanh::LeanObject,
    mut v_a_2260_: *mut crate::leanh::LeanObject,
    mut v_a_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2265_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut v_unused_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2281_: u8 = 0;
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: u8 = 0;
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: usize = 0;
    let mut v___x_2293_: usize = 0;
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___y_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: f64 = 0.0;
    let mut v___x_2306_: f64 = 0.0;
    let mut v___x_2307_: f64 = 0.0;
    let mut v___x_2308_: f64 = 0.0;
    let mut v___x_2309_: f64 = 0.0;
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2318_: u8 = 0;
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: f64 = 0.0;
    let mut v___x_2327_: f64 = 0.0;
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2336_: u8 = 0;
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: usize = 0;
    let mut v___x_2350_: usize = 0;
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: u8 = 0;
    let mut v_a_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2357_: u8 = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2367_: usize = 0;
    let mut v___x_2368_: usize = 0;
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    let mut v_a_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: usize = 0;
    let mut v___x_2389_: usize = 0;
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2263_ = crate::leanh::lean_ctor_get(v_a_2260_, 2);
                v_inheritedTraceOptions_2264_ = crate::leanh::lean_ctor_get(v_a_2260_, 13);
                v_hasTrace_2265_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_2263_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_2266_ = l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef;
                v___x_2267_ = crate::leanh::lean_box(0);
                if v_hasTrace_2265_ == 0 {
                    v___x_2286_ = lean_st_ref_get(v___x_2266_);
                    v___x_2287_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2288_ = lean_array_get_size(v___x_2286_);
                    v___x_2289_ = lean_nat_dec_lt(v___x_2287_, v___x_2288_);
                    if v___x_2289_ == 0 {
                        crate::leanh::lean_dec(v___x_2286_);
                        crate::leanh::lean_dec(v_name_2259_);
                        v___x_2290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2290_, 0, v___x_2267_);
                        return v___x_2290_;
                    } else {
                        if v___x_2289_ == 0 {
                            crate::leanh::lean_dec(v___x_2286_);
                            crate::leanh::lean_dec(v_name_2259_);
                            v___x_2291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2291_, 0, v___x_2267_);
                            return v___x_2291_;
                        } else {
                            v___x_2292_ = 0usize;
                            v___x_2293_ = lean_usize_of_nat(v___x_2288_);
                            v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_2259_, v___x_2286_, v___x_2292_, v___x_2293_, v_a_2260_, v_a_2261_);
                            crate::leanh::lean_dec(v___x_2286_);
                            v___y_2269_ = v___x_2294_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_name_2259_);
                    v___f_2295_ = crate::leanh::lean_alloc_closure(
                        l_Lean_executeReservedNameAction___lam__0___boxed as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2295_, 0, v_name_2259_);
                    v___x_2296_ = l_Lean_executeReservedNameAction___closed__1;
                    v___x_2297_ = l_Lean_executeReservedNameAction___closed__2;
                    v___x_2298_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_executeReservedNameAction___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_executeReservedNameAction___closed__5_once),
                        _init_l_Lean_executeReservedNameAction___closed__5,
                    );
                    v___x_2299_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2264_,
                        v_options_2263_,
                        v___x_2298_,
                    );
                    if v___x_2299_ == 0 {
                        v___x_2380_ = l_Lean_trace_profiler;
                        v___x_2381_ =
                            l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(
                                v_options_2263_,
                                v___x_2380_,
                            );
                        if v___x_2381_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_2295_);
                            v___x_2382_ = lean_st_ref_get(v___x_2266_);
                            v___x_2383_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_2384_ = lean_array_get_size(v___x_2382_);
                            v___x_2385_ = lean_nat_dec_lt(v___x_2383_, v___x_2384_);
                            if v___x_2385_ == 0 {
                                crate::leanh::lean_dec(v___x_2382_);
                                crate::leanh::lean_dec(v_name_2259_);
                                v___x_2386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2386_, 0, v___x_2267_);
                                return v___x_2386_;
                            } else {
                                if v___x_2385_ == 0 {
                                    crate::leanh::lean_dec(v___x_2382_);
                                    crate::leanh::lean_dec(v_name_2259_);
                                    v___x_2387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2387_, 0, v___x_2267_);
                                    return v___x_2387_;
                                } else {
                                    v___x_2388_ = 0usize;
                                    v___x_2389_ = lean_usize_of_nat(v___x_2384_);
                                    v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_2259_, v___x_2382_, v___x_2388_, v___x_2389_, v_a_2260_, v_a_2261_);
                                    crate::leanh::lean_dec(v___x_2382_);
                                    v___y_2269_ = v___x_2390_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            state = 10;
                            continue;
                        }
                    } else {
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2269_) == 0 {
                    v_isSharedCheck_2276_ = (!crate::leanh::lean_is_exclusive(v___y_2269_)) as u8;
                    if v_isSharedCheck_2276_ == 0 {
                        v_unused_2277_ = crate::leanh::lean_ctor_get(v___y_2269_, 0);
                        crate::leanh::lean_dec(v_unused_2277_);
                        v___x_2271_ = v___y_2269_;
                        v_isShared_2272_ = v_isSharedCheck_2276_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_2269_);
                        v___x_2271_ = crate::leanh::lean_box(0);
                        v_isShared_2272_ = v_isSharedCheck_2276_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2278_ = crate::leanh::lean_ctor_get(v___y_2269_, 0);
                    v_isSharedCheck_2285_ = (!crate::leanh::lean_is_exclusive(v___y_2269_)) as u8;
                    if v_isSharedCheck_2285_ == 0 {
                        v___x_2280_ = v___y_2269_;
                        v_isShared_2281_ = v_isSharedCheck_2285_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2278_);
                        crate::leanh::lean_dec(v___y_2269_);
                        v___x_2280_ = crate::leanh::lean_box(0);
                        v_isShared_2281_ = v_isSharedCheck_2285_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2272_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2271_, 0, v___x_2267_);
                    v___x_2274_ = v___x_2271_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2275_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2267_);
                    v___x_2274_ = v_reuseFailAlloc_2275_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2274_;
            }
            4 => {
                if v_isShared_2281_ == 0 {
                    v___x_2283_ = v___x_2280_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
                    v___x_2283_ = v_reuseFailAlloc_2284_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2283_;
            }
            6 => {
                v___x_2304_ = lean_io_mono_nanos_now();
                v___x_2305_ = lean_float_of_nat(v___y_2302_);
                v___x_2306_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_executeReservedNameAction___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_executeReservedNameAction___closed__6_once),
                    _init_l_Lean_executeReservedNameAction___closed__6,
                );
                v___x_2307_ = lean_float_div(v___x_2305_, v___x_2306_);
                v___x_2308_ = lean_float_of_nat(v___x_2304_);
                v___x_2309_ = lean_float_div(v___x_2308_, v___x_2306_);
                v___x_2310_ = crate::leanh::lean_box_float(v___x_2307_);
                v___x_2311_ = crate::leanh::lean_box_float(v___x_2309_);
                v___x_2312_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2312_, 0, v___x_2310_);
                crate::leanh::lean_ctor_set(v___x_2312_, 1, v___x_2311_);
                v___x_2313_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2313_, 0, v_a_2303_);
                crate::leanh::lean_ctor_set(v___x_2313_, 1, v___x_2312_);
                v___x_2314_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_2296_, v_hasTrace_2265_, v___x_2297_, v_options_2263_, v___x_2299_, v___y_2301_, v___f_2295_, v___x_2313_, v_a_2260_, v_a_2261_);
                v___y_2269_ = v___x_2314_;
                state = 1;
                continue;
            }
            7 => {
                v___x_2319_ = crate::leanh::lean_box((v_a_2318_) as usize);
                v___x_2320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2320_, 0, v___x_2319_);
                v___y_2301_ = v___y_2316_;
                v___y_2302_ = v___y_2317_;
                v_a_2303_ = v___x_2320_;
                state = 6;
                continue;
            }
            8 => {
                v___x_2325_ = lean_io_get_num_heartbeats();
                v___x_2326_ = lean_float_of_nat(v___y_2323_);
                v___x_2327_ = lean_float_of_nat(v___x_2325_);
                v___x_2328_ = crate::leanh::lean_box_float(v___x_2326_);
                v___x_2329_ = crate::leanh::lean_box_float(v___x_2327_);
                v___x_2330_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2330_, 0, v___x_2328_);
                crate::leanh::lean_ctor_set(v___x_2330_, 1, v___x_2329_);
                v___x_2331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2331_, 0, v_a_2324_);
                crate::leanh::lean_ctor_set(v___x_2331_, 1, v___x_2330_);
                v___x_2332_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3(v___x_2296_, v_hasTrace_2265_, v___x_2297_, v_options_2263_, v___x_2299_, v___y_2322_, v___f_2295_, v___x_2331_, v_a_2260_, v_a_2261_);
                v___y_2269_ = v___x_2332_;
                state = 1;
                continue;
            }
            9 => {
                v___x_2337_ = crate::leanh::lean_box((v_a_2336_) as usize);
                v___x_2338_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2338_, 0, v___x_2337_);
                v___y_2322_ = v___y_2334_;
                v___y_2323_ = v___y_2335_;
                v_a_2324_ = v___x_2338_;
                state = 8;
                continue;
            }
            10 => {
                v___x_2340_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_executeReservedNameAction_spec__1___redArg(v_a_2261_);
                v_a_2341_ = crate::leanh::lean_ctor_get(v___x_2340_, 0);
                crate::leanh::lean_inc(v_a_2341_);
                crate::leanh::lean_dec_ref(v___x_2340_);
                v___x_2342_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_2343_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(
                    v_options_2263_,
                    v___x_2342_,
                );
                if v___x_2343_ == 0 {
                    v___x_2344_ = lean_io_mono_nanos_now();
                    v___x_2345_ = lean_st_ref_get(v___x_2266_);
                    v___x_2346_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2347_ = lean_array_get_size(v___x_2345_);
                    v___x_2348_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
                    if v___x_2348_ == 0 {
                        crate::leanh::lean_dec(v___x_2345_);
                        crate::leanh::lean_dec(v_name_2259_);
                        v___y_2316_ = v_a_2341_;
                        v___y_2317_ = v___x_2344_;
                        v_a_2318_ = v___x_2343_;
                        state = 7;
                        continue;
                    } else {
                        if v___x_2348_ == 0 {
                            crate::leanh::lean_dec(v___x_2345_);
                            crate::leanh::lean_dec(v_name_2259_);
                            v___y_2316_ = v_a_2341_;
                            v___y_2317_ = v___x_2344_;
                            v_a_2318_ = v___x_2343_;
                            state = 7;
                            continue;
                        } else {
                            v___x_2349_ = 0usize;
                            v___x_2350_ = lean_usize_of_nat(v___x_2347_);
                            v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_2259_, v___x_2345_, v___x_2349_, v___x_2350_, v_a_2260_, v_a_2261_);
                            crate::leanh::lean_dec(v___x_2345_);
                            if crate::leanh::lean_obj_tag(v___x_2351_) == 0 {
                                v_a_2352_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                                crate::leanh::lean_inc(v_a_2352_);
                                crate::leanh::lean_dec_ref_known(v___x_2351_, 1);
                                v___x_2353_ = (crate::leanh::lean_unbox(v_a_2352_) as u8);
                                crate::leanh::lean_dec(v_a_2352_);
                                v___y_2316_ = v_a_2341_;
                                v___y_2317_ = v___x_2344_;
                                v_a_2318_ = v___x_2353_;
                                state = 7;
                                continue;
                            } else {
                                v_a_2354_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                                v_isSharedCheck_2361_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2351_)) as u8;
                                if v_isSharedCheck_2361_ == 0 {
                                    v___x_2356_ = v___x_2351_;
                                    v_isShared_2357_ = v_isSharedCheck_2361_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2354_);
                                    crate::leanh::lean_dec(v___x_2351_);
                                    v___x_2356_ = crate::leanh::lean_box(0);
                                    v_isShared_2357_ = v_isSharedCheck_2361_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_2362_ = lean_io_get_num_heartbeats();
                    v___x_2363_ = lean_st_ref_get(v___x_2266_);
                    v___x_2364_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2365_ = lean_array_get_size(v___x_2363_);
                    v___x_2366_ = lean_nat_dec_lt(v___x_2364_, v___x_2365_);
                    if v___x_2366_ == 0 {
                        crate::leanh::lean_dec(v___x_2363_);
                        crate::leanh::lean_dec(v_name_2259_);
                        v___y_2334_ = v_a_2341_;
                        v___y_2335_ = v___x_2362_;
                        v_a_2336_ = v___x_2366_;
                        state = 9;
                        continue;
                    } else {
                        if v___x_2366_ == 0 {
                            crate::leanh::lean_dec(v___x_2363_);
                            crate::leanh::lean_dec(v_name_2259_);
                            v___y_2334_ = v_a_2341_;
                            v___y_2335_ = v___x_2362_;
                            v_a_2336_ = v___x_2366_;
                            state = 9;
                            continue;
                        } else {
                            v___x_2367_ = 0usize;
                            v___x_2368_ = lean_usize_of_nat(v___x_2365_);
                            v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_executeReservedNameAction_spec__0(v_name_2259_, v___x_2363_, v___x_2367_, v___x_2368_, v_a_2260_, v_a_2261_);
                            crate::leanh::lean_dec(v___x_2363_);
                            if crate::leanh::lean_obj_tag(v___x_2369_) == 0 {
                                v_a_2370_ = crate::leanh::lean_ctor_get(v___x_2369_, 0);
                                crate::leanh::lean_inc(v_a_2370_);
                                crate::leanh::lean_dec_ref_known(v___x_2369_, 1);
                                v___x_2371_ = (crate::leanh::lean_unbox(v_a_2370_) as u8);
                                crate::leanh::lean_dec(v_a_2370_);
                                v___y_2334_ = v_a_2341_;
                                v___y_2335_ = v___x_2362_;
                                v_a_2336_ = v___x_2371_;
                                state = 9;
                                continue;
                            } else {
                                v_a_2372_ = crate::leanh::lean_ctor_get(v___x_2369_, 0);
                                v_isSharedCheck_2379_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2369_)) as u8;
                                if v_isSharedCheck_2379_ == 0 {
                                    v___x_2374_ = v___x_2369_;
                                    v_isShared_2375_ = v_isSharedCheck_2379_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2372_);
                                    crate::leanh::lean_dec(v___x_2369_);
                                    v___x_2374_ = crate::leanh::lean_box(0);
                                    v_isShared_2375_ = v_isSharedCheck_2379_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            11 => {
                if v_isShared_2357_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2356_, 0);
                    v___x_2359_ = v___x_2356_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
                    v___x_2359_ = v_reuseFailAlloc_2360_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_2301_ = v_a_2341_;
                v___y_2302_ = v___x_2344_;
                v_a_2303_ = v___x_2359_;
                state = 6;
                continue;
            }
            13 => {
                if v_isShared_2375_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2374_, 0);
                    v___x_2377_ = v___x_2374_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
                    v___x_2377_ = v_reuseFailAlloc_2378_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_2322_ = v_a_2341_;
                v___y_2323_ = v___x_2362_;
                v_a_2324_ = v___x_2377_;
                state = 8;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_executeReservedNameAction___boxed(
    mut v_name_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_a_2393_: *mut crate::leanh::LeanObject,
    mut v_a_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Lean_executeReservedNameAction(v_name_2391_, v_a_2392_, v_a_2393_);
    crate::leanh::lean_dec(v_a_2393_);
    crate::leanh::lean_dec_ref(v_a_2392_);
    return v_res_2395_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(
    mut v_00_u03b1_2396_: *mut crate::leanh::LeanObject,
    mut v_x_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2401_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___redArg(v_x_2397_);
    return v___x_2401_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5___boxed(
    mut v_00_u03b1_2402_: *mut crate::leanh::LeanObject,
    mut v_x_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__5(v_00_u03b1_2402_, v_x_2403_, v___y_2404_, v___y_2405_);
    crate::leanh::lean_dec(v___y_2405_);
    crate::leanh::lean_dec_ref(v___y_2404_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(
    mut v___y_2415_: u8,
    mut v_suppressElabErrors_2416_: u8,
    mut v_x_2417_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2417_) == 1 {
        let mut v_pre_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2418_ = crate::leanh::lean_ctor_get(v_x_2417_, 0);
        match crate::leanh::lean_obj_tag(v_pre_2418_) {
            1 => {
                let mut v_pre_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_2419_ = crate::leanh::lean_ctor_get(v_pre_2418_, 0);
                match crate::leanh::lean_obj_tag(v_pre_2419_) {
                    0 => {
                        let mut v_str_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2423_: u8 = 0;
                        v_str_2420_ = crate::leanh::lean_ctor_get(v_x_2417_, 1);
                        v_str_2421_ = crate::leanh::lean_ctor_get(v_pre_2418_, 1);
                        v___x_2422_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__0;
                        v___x_2423_ = lean_string_dec_eq(v_str_2421_, v___x_2422_);
                        if v___x_2423_ == 0 {
                            let mut v___x_2424_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2425_: u8 = 0;
                            v___x_2424_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__1;
                            v___x_2425_ = lean_string_dec_eq(v_str_2421_, v___x_2424_);
                            if v___x_2425_ == 0 {
                                return v___y_2415_;
                            } else {
                                let mut v___x_2426_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2427_: u8 = 0;
                                v___x_2426_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__2;
                                v___x_2427_ = lean_string_dec_eq(v_str_2420_, v___x_2426_);
                                if v___x_2427_ == 0 {
                                    return v___y_2415_;
                                } else {
                                    return v_suppressElabErrors_2416_;
                                }
                            }
                        } else {
                            let mut v___x_2428_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2429_: u8 = 0;
                            v___x_2428_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__3;
                            v___x_2429_ = lean_string_dec_eq(v_str_2420_, v___x_2428_);
                            if v___x_2429_ == 0 {
                                return v___y_2415_;
                            } else {
                                return v_suppressElabErrors_2416_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2430_ = crate::leanh::lean_ctor_get(v_pre_2419_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_2430_) == 0 {
                            let mut v_str_2431_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2432_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2433_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2434_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2435_: u8 = 0;
                            v_str_2431_ = crate::leanh::lean_ctor_get(v_x_2417_, 1);
                            v_str_2432_ = crate::leanh::lean_ctor_get(v_pre_2418_, 1);
                            v_str_2433_ = crate::leanh::lean_ctor_get(v_pre_2419_, 1);
                            v___x_2434_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__4;
                            v___x_2435_ = lean_string_dec_eq(v_str_2433_, v___x_2434_);
                            if v___x_2435_ == 0 {
                                return v___y_2415_;
                            } else {
                                let mut v___x_2436_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2437_: u8 = 0;
                                v___x_2436_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__5;
                                v___x_2437_ = lean_string_dec_eq(v_str_2432_, v___x_2436_);
                                if v___x_2437_ == 0 {
                                    return v___y_2415_;
                                } else {
                                    let mut v___x_2438_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2439_: u8 = 0;
                                    v___x_2438_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___closed__6;
                                    v___x_2439_ = lean_string_dec_eq(v_str_2431_, v___x_2438_);
                                    if v___x_2439_ == 0 {
                                        return v___y_2415_;
                                    } else {
                                        return v_suppressElabErrors_2416_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2415_;
                        }
                    }
                    _ => {
                        return v___y_2415_;
                    }
                }
            }
            0 => {
                let mut v_str_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2442_: u8 = 0;
                v_str_2440_ = crate::leanh::lean_ctor_get(v_x_2417_, 1);
                v___x_2441_ = l_Lean_executeReservedNameAction___closed__3;
                v___x_2442_ = lean_string_dec_eq(v_str_2440_, v___x_2441_);
                if v___x_2442_ == 0 {
                    return v___y_2415_;
                } else {
                    return v_suppressElabErrors_2416_;
                }
            }
            _ => {
                return v___y_2415_;
            }
        }
    } else {
        return v___y_2415_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed(
    mut v___y_2443_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_2444_: *mut crate::leanh::LeanObject,
    mut v_x_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4708__boxed_2446_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2447_: u8 = 0;
    let mut v_res_2448_: u8 = 0;
    let mut v_r_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_4708__boxed_2446_ = (crate::leanh::lean_unbox(v___y_2443_) as u8);
    v_suppressElabErrors_boxed_2447_ = (crate::leanh::lean_unbox(v_suppressElabErrors_2444_) as u8);
    v_res_2448_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0(v___y_4708__boxed_2446_, v_suppressElabErrors_boxed_2447_, v_x_2445_);
    crate::leanh::lean_dec(v_x_2445_);
    v_r_2449_ = crate::leanh::lean_box((v_res_2448_) as usize);
    return v_r_2449_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(
    mut v_ref_2450_: *mut crate::leanh::LeanObject,
    mut v_msgData_2451_: *mut crate::leanh::LeanObject,
    mut v_severity_2452_: u8,
    mut v_isSilent_2453_: u8,
    mut v___y_2454_: *mut crate::leanh::LeanObject,
    mut v___y_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2458_: u8 = 0;
    let mut v___y_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2462_: u8 = 0;
    let mut v___y_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2481_: u8 = 0;
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut v___y_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: u8 = 0;
    let mut v___y_2497_: u8 = 0;
    let mut v___y_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: u8 = 0;
    let mut v___y_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: u8 = 0;
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2517_: u8 = 0;
    let mut v___y_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: u8 = 0;
    let mut v___y_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2524_: u8 = 0;
    let mut v___y_2525_: u8 = 0;
    let mut v___y_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2532_: u8 = 0;
    let mut v___y_2533_: u8 = 0;
    let mut v___y_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2536_: u8 = 0;
    let mut v_ref_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v___y_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: u8 = 0;
    let mut v___y_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2548_: u8 = 0;
    let mut v___y_2549_: u8 = 0;
    let mut v___y_2551_: u8 = 0;
    let mut v_fileName_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2556_: u8 = 0;
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: u8 = 0;
    let mut v___x_2561_: u8 = 0;
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: u8 = 0;
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: u8 = 0;
    let mut v___x_2567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2541_ = 2;
                v___x_2566_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2452_, v___x_2541_);
                if v___x_2566_ == 0 {
                    v___y_2551_ = v___x_2566_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_2451_);
                    v___x_2567_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2451_);
                    v___y_2551_ = v___x_2567_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2467_ = lean_st_ref_take(v___y_2466_);
                v_currNamespace_2468_ = crate::leanh::lean_ctor_get(v___y_2465_, 6);
                v_openDecls_2469_ = crate::leanh::lean_ctor_get(v___y_2465_, 7);
                v_env_2470_ = crate::leanh::lean_ctor_get(v___x_2467_, 0);
                v_nextMacroScope_2471_ = crate::leanh::lean_ctor_get(v___x_2467_, 1);
                v_ngen_2472_ = crate::leanh::lean_ctor_get(v___x_2467_, 2);
                v_auxDeclNGen_2473_ = crate::leanh::lean_ctor_get(v___x_2467_, 3);
                v_traceState_2474_ = crate::leanh::lean_ctor_get(v___x_2467_, 4);
                v_cache_2475_ = crate::leanh::lean_ctor_get(v___x_2467_, 5);
                v_messages_2476_ = crate::leanh::lean_ctor_get(v___x_2467_, 6);
                v_infoState_2477_ = crate::leanh::lean_ctor_get(v___x_2467_, 7);
                v_snapshotTasks_2478_ = crate::leanh::lean_ctor_get(v___x_2467_, 8);
                v_isSharedCheck_2492_ = (!crate::leanh::lean_is_exclusive(v___x_2467_)) as u8;
                if v_isSharedCheck_2492_ == 0 {
                    v___x_2480_ = v___x_2467_;
                    v_isShared_2481_ = v_isSharedCheck_2492_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2478_);
                    crate::leanh::lean_inc(v_infoState_2477_);
                    crate::leanh::lean_inc(v_messages_2476_);
                    crate::leanh::lean_inc(v_cache_2475_);
                    crate::leanh::lean_inc(v_traceState_2474_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2473_);
                    crate::leanh::lean_inc(v_ngen_2472_);
                    crate::leanh::lean_inc(v_nextMacroScope_2471_);
                    crate::leanh::lean_inc(v_env_2470_);
                    crate::leanh::lean_dec(v___x_2467_);
                    v___x_2480_ = crate::leanh::lean_box(0);
                    v_isShared_2481_ = v_isSharedCheck_2492_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_2469_);
                crate::leanh::lean_inc(v_currNamespace_2468_);
                v___x_2482_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2482_, 0, v_currNamespace_2468_);
                crate::leanh::lean_ctor_set(v___x_2482_, 1, v_openDecls_2469_);
                v___x_2483_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2483_, 0, v___x_2482_);
                crate::leanh::lean_ctor_set(v___x_2483_, 1, v___y_2460_);
                crate::leanh::lean_inc_ref(v___y_2464_);
                crate::leanh::lean_inc_ref(v___y_2459_);
                v___x_2484_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_2484_, 0, v___y_2459_);
                crate::leanh::lean_ctor_set(v___x_2484_, 1, v___y_2461_);
                crate::leanh::lean_ctor_set(v___x_2484_, 2, v___y_2463_);
                crate::leanh::lean_ctor_set(v___x_2484_, 3, v___y_2464_);
                crate::leanh::lean_ctor_set(v___x_2484_, 4, v___x_2483_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2484_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_2458_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2484_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2462_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2484_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2453_,
                );
                v___x_2485_ = l_Lean_MessageLog_add(v___x_2484_, v_messages_2476_);
                if v_isShared_2481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2480_, 6, v___x_2485_);
                    v___x_2487_ = v___x_2480_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2491_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_env_2470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_nextMacroScope_2471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_ngen_2472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_auxDeclNGen_2473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_traceState_2474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 5, v_cache_2475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 6, v___x_2485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 7, v_infoState_2477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2491_, 8, v_snapshotTasks_2478_);
                    v___x_2487_ = v_reuseFailAlloc_2491_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2488_ = lean_st_ref_set(v___y_2466_, v___x_2487_);
                v___x_2489_ = crate::leanh::lean_box(0);
                v___x_2490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2490_, 0, v___x_2489_);
                return v___x_2490_;
            }
            4 => {
                v___x_2502_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2451_,
                    );
                v___x_2503_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(v___x_2502_, v___y_2454_, v___y_2455_);
                v_a_2504_ = crate::leanh::lean_ctor_get(v___x_2503_, 0);
                v_isSharedCheck_2517_ = (!crate::leanh::lean_is_exclusive(v___x_2503_)) as u8;
                if v_isSharedCheck_2517_ == 0 {
                    v___x_2506_ = v___x_2503_;
                    v_isShared_2507_ = v_isSharedCheck_2517_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2504_);
                    crate::leanh::lean_dec(v___x_2503_);
                    v___x_2506_ = crate::leanh::lean_box(0);
                    v_isShared_2507_ = v_isSharedCheck_2517_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_2495_, 2);
                v___x_2508_ = l_Lean_FileMap_toPosition(v___y_2495_, v___y_2499_);
                crate::leanh::lean_dec(v___y_2499_);
                v___x_2509_ = l_Lean_FileMap_toPosition(v___y_2495_, v___y_2501_);
                crate::leanh::lean_dec(v___y_2501_);
                v___x_2510_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2510_, 0, v___x_2509_);
                v___x_2511_ = l_Lean_executeReservedNameAction___closed__2;
                if v___y_2497_ == 0 {
                    crate::leanh::lean_del_object(v___x_2506_);
                    crate::leanh::lean_dec_ref(v___y_2494_);
                    v___y_2458_ = v___y_2496_;
                    v___y_2459_ = v___y_2498_;
                    v___y_2460_ = v_a_2504_;
                    v___y_2461_ = v___x_2508_;
                    v___y_2462_ = v___y_2500_;
                    v___y_2463_ = v___x_2510_;
                    v___y_2464_ = v___x_2511_;
                    v___y_2465_ = v___y_2454_;
                    v___y_2466_ = v___y_2455_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2504_);
                    v___x_2512_ = l_Lean_MessageData_hasTag(v___y_2494_, v_a_2504_);
                    if v___x_2512_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2510_, 1);
                        crate::leanh::lean_dec_ref(v___x_2508_);
                        crate::leanh::lean_dec(v_a_2504_);
                        v___x_2513_ = crate::leanh::lean_box(0);
                        if v_isShared_2507_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2506_, 0, v___x_2513_);
                            v___x_2515_ = v___x_2506_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2516_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
                            v___x_2515_ = v_reuseFailAlloc_2516_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2506_);
                        v___y_2458_ = v___y_2496_;
                        v___y_2459_ = v___y_2498_;
                        v___y_2460_ = v_a_2504_;
                        v___y_2461_ = v___x_2508_;
                        v___y_2462_ = v___y_2500_;
                        v___y_2463_ = v___x_2510_;
                        v___y_2464_ = v___x_2511_;
                        v___y_2465_ = v___y_2454_;
                        v___y_2466_ = v___y_2455_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2515_;
            }
            7 => {
                v___x_2527_ = l_Lean_Syntax_getTailPos_x3f(v___y_2521_, v___y_2522_);
                crate::leanh::lean_dec(v___y_2521_);
                if crate::leanh::lean_obj_tag(v___x_2527_) == 0 {
                    crate::leanh::lean_inc(v___y_2526_);
                    v___y_2494_ = v___y_2519_;
                    v___y_2495_ = v___y_2520_;
                    v___y_2496_ = v___y_2522_;
                    v___y_2497_ = v___y_2524_;
                    v___y_2498_ = v___y_2523_;
                    v___y_2499_ = v___y_2526_;
                    v___y_2500_ = v___y_2525_;
                    v___y_2501_ = v___y_2526_;
                    state = 4;
                    continue;
                } else {
                    v_val_2528_ = crate::leanh::lean_ctor_get(v___x_2527_, 0);
                    crate::leanh::lean_inc(v_val_2528_);
                    crate::leanh::lean_dec_ref_known(v___x_2527_, 1);
                    v___y_2494_ = v___y_2519_;
                    v___y_2495_ = v___y_2520_;
                    v___y_2496_ = v___y_2522_;
                    v___y_2497_ = v___y_2524_;
                    v___y_2498_ = v___y_2523_;
                    v___y_2499_ = v___y_2526_;
                    v___y_2500_ = v___y_2525_;
                    v___y_2501_ = v_val_2528_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2537_ = l_Lean_replaceRef(v_ref_2450_, v___y_2535_);
                v___x_2538_ = l_Lean_Syntax_getPos_x3f(v_ref_2537_, v___y_2532_);
                if crate::leanh::lean_obj_tag(v___x_2538_) == 0 {
                    v___x_2539_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2519_ = v___y_2530_;
                    v___y_2520_ = v___y_2531_;
                    v___y_2521_ = v_ref_2537_;
                    v___y_2522_ = v___y_2532_;
                    v___y_2523_ = v___y_2534_;
                    v___y_2524_ = v___y_2533_;
                    v___y_2525_ = v___y_2536_;
                    v___y_2526_ = v___x_2539_;
                    state = 7;
                    continue;
                } else {
                    v_val_2540_ = crate::leanh::lean_ctor_get(v___x_2538_, 0);
                    crate::leanh::lean_inc(v_val_2540_);
                    crate::leanh::lean_dec_ref_known(v___x_2538_, 1);
                    v___y_2519_ = v___y_2530_;
                    v___y_2520_ = v___y_2531_;
                    v___y_2521_ = v_ref_2537_;
                    v___y_2522_ = v___y_2532_;
                    v___y_2523_ = v___y_2534_;
                    v___y_2524_ = v___y_2533_;
                    v___y_2525_ = v___y_2536_;
                    v___y_2526_ = v_val_2540_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2549_ == 0 {
                    v___y_2530_ = v___y_2543_;
                    v___y_2531_ = v___y_2544_;
                    v___y_2532_ = v___y_2548_;
                    v___y_2533_ = v___y_2546_;
                    v___y_2534_ = v___y_2545_;
                    v___y_2535_ = v___y_2547_;
                    v___y_2536_ = v_severity_2452_;
                    state = 8;
                    continue;
                } else {
                    v___y_2530_ = v___y_2543_;
                    v___y_2531_ = v___y_2544_;
                    v___y_2532_ = v___y_2548_;
                    v___y_2533_ = v___y_2546_;
                    v___y_2534_ = v___y_2545_;
                    v___y_2535_ = v___y_2547_;
                    v___y_2536_ = v___x_2541_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2551_ == 0 {
                    v_fileName_2552_ = crate::leanh::lean_ctor_get(v___y_2454_, 0);
                    v_fileMap_2553_ = crate::leanh::lean_ctor_get(v___y_2454_, 1);
                    v_options_2554_ = crate::leanh::lean_ctor_get(v___y_2454_, 2);
                    v_ref_2555_ = crate::leanh::lean_ctor_get(v___y_2454_, 5);
                    v_suppressElabErrors_2556_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2454_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2557_ = crate::leanh::lean_box((v___y_2551_) as usize);
                    v___x_2558_ = crate::leanh::lean_box((v_suppressElabErrors_2556_) as usize);
                    v___f_2559_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_2559_, 0, v___x_2557_);
                    crate::leanh::lean_closure_set(v___f_2559_, 1, v___x_2558_);
                    v___x_2560_ = 1;
                    v___x_2561_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2452_, v___x_2560_);
                    if v___x_2561_ == 0 {
                        v___y_2543_ = v___f_2559_;
                        v___y_2544_ = v_fileMap_2553_;
                        v___y_2545_ = v_fileName_2552_;
                        v___y_2546_ = v_suppressElabErrors_2556_;
                        v___y_2547_ = v_ref_2555_;
                        v___y_2548_ = v___y_2551_;
                        v___y_2549_ = v___x_2561_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2562_ = l_Lean_warningAsError;
                        v___x_2563_ =
                            l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(
                                v_options_2554_,
                                v___x_2562_,
                            );
                        v___y_2543_ = v___f_2559_;
                        v___y_2544_ = v_fileMap_2553_;
                        v___y_2545_ = v_fileName_2552_;
                        v___y_2546_ = v_suppressElabErrors_2556_;
                        v___y_2547_ = v_ref_2555_;
                        v___y_2548_ = v___y_2551_;
                        v___y_2549_ = v___x_2563_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_2451_);
                    v___x_2564_ = crate::leanh::lean_box(0);
                    v___x_2565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2565_, 0, v___x_2564_);
                    return v___x_2565_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1___boxed(
    mut v_ref_2568_: *mut crate::leanh::LeanObject,
    mut v_msgData_2569_: *mut crate::leanh::LeanObject,
    mut v_severity_2570_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
    mut v___y_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2575_: u8 = 0;
    let mut v_isSilent_boxed_2576_: u8 = 0;
    let mut v_res_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2575_ = (crate::leanh::lean_unbox(v_severity_2570_) as u8);
    v_isSilent_boxed_2576_ = (crate::leanh::lean_unbox(v_isSilent_2571_) as u8);
    v_res_2577_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_2568_, v_msgData_2569_, v_severity_boxed_2575_, v_isSilent_boxed_2576_, v___y_2572_, v___y_2573_);
    crate::leanh::lean_dec(v___y_2573_);
    crate::leanh::lean_dec_ref(v___y_2572_);
    crate::leanh::lean_dec(v_ref_2568_);
    return v_res_2577_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(
    mut v_msgData_2578_: *mut crate::leanh::LeanObject,
    mut v_severity_2579_: u8,
    mut v_isSilent_2580_: u8,
    mut v___y_2581_: *mut crate::leanh::LeanObject,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2584_ = crate::leanh::lean_ctor_get(v___y_2581_, 5);
    v___x_2585_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0_spec__1(v_ref_2584_, v_msgData_2578_, v_severity_2579_, v_isSilent_2580_, v___y_2581_, v___y_2582_);
    return v___x_2585_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0___boxed(
    mut v_msgData_2586_: *mut crate::leanh::LeanObject,
    mut v_severity_2587_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
    mut v___y_2590_: *mut crate::leanh::LeanObject,
    mut v___y_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2592_: u8 = 0;
    let mut v_isSilent_boxed_2593_: u8 = 0;
    let mut v_res_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2592_ = (crate::leanh::lean_unbox(v_severity_2587_) as u8);
    v_isSilent_boxed_2593_ = (crate::leanh::lean_unbox(v_isSilent_2588_) as u8);
    v_res_2594_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(
        v_msgData_2586_,
        v_severity_boxed_2592_,
        v_isSilent_boxed_2593_,
        v___y_2589_,
        v___y_2590_,
    );
    crate::leanh::lean_dec(v___y_2590_);
    crate::leanh::lean_dec_ref(v___y_2589_);
    return v_res_2594_;
}
pub unsafe fn l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(
    mut v_msgData_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2600_: u8 = 0;
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2599_ = 2;
    v___x_2600_ = 0;
    v___x_2601_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(
        v_msgData_2595_,
        v___x_2599_,
        v___x_2600_,
        v___y_2596_,
        v___y_2597_,
    );
    return v___x_2601_;
}
pub unsafe fn l_Lean_logError___at___00Lean_realizeGlobalName_spec__0___boxed(
    mut v_msgData_2602_: *mut crate::leanh::LeanObject,
    mut v___y_2603_: *mut crate::leanh::LeanObject,
    mut v___y_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2606_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(
        v_msgData_2602_,
        v___y_2603_,
        v___y_2604_,
    );
    crate::leanh::lean_dec(v___y_2604_);
    crate::leanh::lean_dec_ref(v___y_2603_);
    return v_res_2606_;
}
pub unsafe fn _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2608_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__0;
    v___x_2609_ = l_Lean_stringToMessageData(v___x_2608_);
    return v___x_2609_;
}
pub unsafe fn _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2611_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__2;
    v___x_2612_ = l_Lean_stringToMessageData(v___x_2611_);
    return v___x_2612_;
}
pub unsafe fn l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(
    mut v_id_2613_: *mut crate::leanh::LeanObject,
    mut v_x_2614_: *mut crate::leanh::LeanObject,
    mut v_x_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2624_: u8 = 0;
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: u8 = 0;
    let mut v___x_2634_: u8 = 0;
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2642_: u8 = 0;
    let mut v_a_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___y_2648_: u8 = 0;
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2663_: u8 = 0;
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2667_: u8 = 0;
    let mut v_reuseFailAlloc_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2673_: u8 = 0;
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut v_isSharedCheck_2675_: u8 = 0;
    let mut v_unused_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2614_) == 0 {
                    crate::leanh::lean_dec(v_id_2613_);
                    v___x_2619_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2619_, 0, v_x_2615_);
                    return v___x_2619_;
                } else {
                    v_head_2620_ = crate::leanh::lean_ctor_get(v_x_2614_, 0);
                    v_tail_2621_ = crate::leanh::lean_ctor_get(v_x_2614_, 1);
                    v_isSharedCheck_2678_ = (!crate::leanh::lean_is_exclusive(v_x_2614_)) as u8;
                    if v_isSharedCheck_2678_ == 0 {
                        v___x_2623_ = v_x_2614_;
                        v_isShared_2624_ = v_isSharedCheck_2678_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2621_);
                        crate::leanh::lean_inc(v_head_2620_);
                        crate::leanh::lean_dec(v_x_2614_);
                        v___x_2623_ = crate::leanh::lean_box(0);
                        v_isShared_2624_ = v_isSharedCheck_2678_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2630_ = crate::leanh::lean_ctor_get(v_head_2620_, 0);
                v___x_2631_ = lean_st_ref_get(v___y_2617_);
                v_env_2632_ = crate::leanh::lean_ctor_get(v___x_2631_, 0);
                crate::leanh::lean_inc_ref(v_env_2632_);
                crate::leanh::lean_dec(v___x_2631_);
                v___x_2633_ = 1;
                crate::leanh::lean_inc(v_fst_2630_);
                v___x_2634_ = l_Lean_Environment_contains(v_env_2632_, v_fst_2630_, v___x_2633_);
                if v___x_2634_ == 0 {
                    crate::leanh::lean_inc(v_fst_2630_);
                    v___x_2635_ =
                        l_Lean_executeReservedNameAction(v_fst_2630_, v___y_2616_, v___y_2617_);
                    if crate::leanh::lean_obj_tag(v___x_2635_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2635_, 1);
                        v___x_2636_ = lean_st_ref_get(v___y_2617_);
                        v_env_2637_ = crate::leanh::lean_ctor_get(v___x_2636_, 0);
                        crate::leanh::lean_inc_ref(v_env_2637_);
                        crate::leanh::lean_dec(v___x_2636_);
                        v___x_2638_ = l_Lean_Environment_containsOnBranch(v_env_2637_, v_fst_2630_);
                        crate::leanh::lean_dec_ref(v_env_2637_);
                        if v___x_2638_ == 0 {
                            crate::leanh::lean_del_object(v___x_2623_);
                            crate::leanh::lean_dec(v_head_2620_);
                            v_x_2614_ = v_tail_2621_;
                            state = 0;
                            continue;
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2623_);
                        v_isSharedCheck_2675_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2620_)) as u8;
                        if v_isSharedCheck_2675_ == 0 {
                            v_unused_2676_ = crate::leanh::lean_ctor_get(v_head_2620_, 1);
                            crate::leanh::lean_dec(v_unused_2676_);
                            v_unused_2677_ = crate::leanh::lean_ctor_get(v_head_2620_, 0);
                            crate::leanh::lean_dec(v_unused_2677_);
                            v___x_2641_ = v_head_2620_;
                            v_isShared_2642_ = v_isSharedCheck_2675_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_head_2620_);
                            v___x_2641_ = crate::leanh::lean_box(0);
                            v_isShared_2642_ = v_isSharedCheck_2675_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2623_, 1, v_x_2615_);
                    v___x_2627_ = v___x_2623_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2629_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_head_2620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_x_2615_);
                    v___x_2627_ = v_reuseFailAlloc_2629_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_x_2614_ = v_tail_2621_;
                v_x_2615_ = v___x_2627_;
                state = 0;
                continue;
            }
            4 => {
                v_a_2643_ = crate::leanh::lean_ctor_get(v___x_2635_, 0);
                v_isSharedCheck_2674_ = (!crate::leanh::lean_is_exclusive(v___x_2635_)) as u8;
                if v_isSharedCheck_2674_ == 0 {
                    v___x_2645_ = v___x_2635_;
                    v_isShared_2646_ = v_isSharedCheck_2674_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2643_);
                    crate::leanh::lean_dec(v___x_2635_);
                    v___x_2645_ = crate::leanh::lean_box(0);
                    v_isShared_2646_ = v_isSharedCheck_2674_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2672_ = l_Lean_Exception_isInterrupt(v_a_2643_);
                if v___x_2672_ == 0 {
                    crate::leanh::lean_inc(v_a_2643_);
                    v___x_2673_ = l_Lean_Exception_isRuntime(v_a_2643_);
                    v___y_2648_ = v___x_2673_;
                    state = 6;
                    continue;
                } else {
                    v___y_2648_ = v___x_2672_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v___y_2648_ == 0 {
                    crate::leanh::lean_del_object(v___x_2645_);
                    v___x_2649_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1), core::ptr::addr_of_mut!(l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1_once), _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__1);
                    crate::leanh::lean_inc(v_id_2613_);
                    v___x_2650_ = l_Lean_MessageData_ofName(v_id_2613_);
                    if v_isShared_2642_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2641_, 7);
                        crate::leanh::lean_ctor_set(v___x_2641_, 1, v___x_2650_);
                        crate::leanh::lean_ctor_set(v___x_2641_, 0, v___x_2649_);
                        v___x_2652_ = v___x_2641_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2668_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2649_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2668_, 1, v___x_2650_);
                        v___x_2652_ = v_reuseFailAlloc_2668_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2641_);
                    crate::leanh::lean_dec(v_tail_2621_);
                    crate::leanh::lean_dec(v_x_2615_);
                    crate::leanh::lean_dec(v_id_2613_);
                    if v_isShared_2646_ == 0 {
                        v___x_2670_ = v___x_2645_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2643_);
                        v___x_2670_ = v_reuseFailAlloc_2671_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2653_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3_once
                    ),
                    _init_l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___closed__3,
                );
                v___x_2654_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2654_, 0, v___x_2652_);
                crate::leanh::lean_ctor_set(v___x_2654_, 1, v___x_2653_);
                v___x_2655_ = l_Lean_Exception_toMessageData(v_a_2643_);
                v___x_2656_ = l_Lean_indentD(v___x_2655_);
                v___x_2657_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2657_, 0, v___x_2654_);
                crate::leanh::lean_ctor_set(v___x_2657_, 1, v___x_2656_);
                v___x_2658_ = l_Lean_logError___at___00Lean_realizeGlobalName_spec__0(
                    v___x_2657_,
                    v___y_2616_,
                    v___y_2617_,
                );
                if crate::leanh::lean_obj_tag(v___x_2658_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2658_, 1);
                    v_x_2614_ = v_tail_2621_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tail_2621_);
                    crate::leanh::lean_dec(v_x_2615_);
                    crate::leanh::lean_dec(v_id_2613_);
                    v_a_2660_ = crate::leanh::lean_ctor_get(v___x_2658_, 0);
                    v_isSharedCheck_2667_ = (!crate::leanh::lean_is_exclusive(v___x_2658_)) as u8;
                    if v_isSharedCheck_2667_ == 0 {
                        v___x_2662_ = v___x_2658_;
                        v_isShared_2663_ = v_isSharedCheck_2667_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2660_);
                        crate::leanh::lean_dec(v___x_2658_);
                        v___x_2662_ = crate::leanh::lean_box(0);
                        v_isShared_2663_ = v_isSharedCheck_2667_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2663_ == 0 {
                    v___x_2665_ = v___x_2662_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2666_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
                    v___x_2665_ = v_reuseFailAlloc_2666_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2665_;
            }
            10 => {
                return v___x_2670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2___boxed(
    mut v_id_2679_: *mut crate::leanh::LeanObject,
    mut v_x_2680_: *mut crate::leanh::LeanObject,
    mut v_x_2681_: *mut crate::leanh::LeanObject,
    mut v___y_2682_: *mut crate::leanh::LeanObject,
    mut v___y_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2685_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(
        v_id_2679_,
        v_x_2680_,
        v_x_2681_,
        v___y_2682_,
        v___y_2683_,
    );
    crate::leanh::lean_dec(v___y_2683_);
    crate::leanh::lean_dec_ref(v___y_2682_);
    return v_res_2685_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(
    mut v_x_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2686_) == 0 {
                    v___x_2687_ = crate::leanh::lean_box(0);
                    return v___x_2687_;
                } else {
                    v_head_2688_ = crate::leanh::lean_ctor_get(v_x_2686_, 0);
                    v_tail_2689_ = crate::leanh::lean_ctor_get(v_x_2686_, 1);
                    v_fst_2690_ = crate::leanh::lean_ctor_get(v_head_2688_, 0);
                    v___x_2691_ = l_Lean_isPrivateName(v_fst_2690_);
                    if v___x_2691_ == 0 {
                        v_x_2686_ = v_tail_2689_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_head_2688_);
                        v___x_2693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2693_, 0, v_head_2688_);
                        return v___x_2693_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2___boxed(
    mut v_x_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_x_2694_);
    crate::leanh::lean_dec(v_x_2694_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(
    mut v_msgData_2696_: *mut crate::leanh::LeanObject,
    mut v___y_2697_: *mut crate::leanh::LeanObject,
    mut v___y_2698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2700_: u8 = 0;
    let mut v___x_2701_: u8 = 0;
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2700_ = 1;
    v___x_2701_ = 0;
    v___x_2702_ = l_Lean_log___at___00Lean_logError___at___00Lean_realizeGlobalName_spec__0_spec__0(
        v_msgData_2696_,
        v___x_2700_,
        v___x_2701_,
        v___y_2697_,
        v___y_2698_,
    );
    return v___x_2702_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6___boxed(
    mut v_msgData_2703_: *mut crate::leanh::LeanObject,
    mut v___y_2704_: *mut crate::leanh::LeanObject,
    mut v___y_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2707_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v_msgData_2703_, v___y_2704_, v___y_2705_);
    crate::leanh::lean_dec(v___y_2705_);
    crate::leanh::lean_dec_ref(v___y_2704_);
    return v_res_2707_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(
    mut v_opt_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_2711_ = crate::leanh::lean_ctor_get(v___y_2709_, 2);
    v___x_2712_ = l_Lean_Option_get___at___00Lean_executeReservedNameAction_spec__2(
        v_options_2711_,
        v_opt_2708_,
    );
    v___x_2713_ = crate::leanh::lean_box((v___x_2712_) as usize);
    v___x_2714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2714_, 0, v___x_2713_);
    return v___x_2714_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_opt_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_2715_, v___y_2716_);
    crate::leanh::lean_dec_ref(v___y_2716_);
    crate::leanh::lean_dec_ref(v_opt_2715_);
    return v_res_2718_;
}
pub unsafe fn _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2720_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__0;
    v___x_2721_ = l_Lean_stringToMessageData(v___x_2720_);
    return v___x_2721_;
}
pub unsafe fn _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__2;
    v___x_2724_ = l_Lean_stringToMessageData(v___x_2723_);
    return v___x_2724_;
}
pub unsafe fn l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(
    mut v_id_2725_: *mut crate::leanh::LeanObject,
    mut v___y_2726_: *mut crate::leanh::LeanObject,
    mut v___y_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2736_: u8 = 0;
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2742_: u8 = 0;
    let mut v___x_2743_: u8 = 0;
    let mut v___x_2744_: u8 = 0;
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2729_ = lean_st_ref_get(v___y_2727_);
                v_env_2730_ = crate::leanh::lean_ctor_get(v___x_2729_, 0);
                crate::leanh::lean_inc_ref(v_env_2730_);
                crate::leanh::lean_dec(v___x_2729_);
                v___x_2731_ = l_Lean_ResolveName_backward_privateInPublic_warn;
                v___x_2732_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v___x_2731_, v___y_2726_);
                v_a_2733_ = crate::leanh::lean_ctor_get(v___x_2732_, 0);
                v_isSharedCheck_2752_ = (!crate::leanh::lean_is_exclusive(v___x_2732_)) as u8;
                if v_isSharedCheck_2752_ == 0 {
                    v___x_2735_ = v___x_2732_;
                    v_isShared_2736_ = v_isSharedCheck_2752_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2733_);
                    crate::leanh::lean_dec(v___x_2732_);
                    v___x_2735_ = crate::leanh::lean_box(0);
                    v_isShared_2736_ = v_isSharedCheck_2752_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_isExporting_2742_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_2730_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_2730_);
                if v_isExporting_2742_ == 0 {
                    crate::leanh::lean_dec(v_a_2733_);
                    crate::leanh::lean_dec(v_id_2725_);
                    state = 2;
                    continue;
                } else {
                    v___x_2743_ = l_Lean_isPrivateName(v_id_2725_);
                    if v___x_2743_ == 0 {
                        crate::leanh::lean_dec(v_a_2733_);
                        crate::leanh::lean_dec(v_id_2725_);
                        state = 2;
                        continue;
                    } else {
                        v___x_2744_ = (crate::leanh::lean_unbox(v_a_2733_) as u8);
                        crate::leanh::lean_dec(v_a_2733_);
                        if v___x_2744_ == 0 {
                            crate::leanh::lean_dec(v_id_2725_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_2735_);
                            v___x_2745_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1_once), _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__1);
                            v___x_2746_ = 0;
                            v___x_2747_ = l_Lean_MessageData_ofConstName(v_id_2725_, v___x_2746_);
                            v___x_2748_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2748_, 0, v___x_2745_);
                            crate::leanh::lean_ctor_set(v___x_2748_, 1, v___x_2747_);
                            v___x_2749_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3_once), _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___closed__3);
                            v___x_2750_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2750_, 0, v___x_2748_);
                            crate::leanh::lean_ctor_set(v___x_2750_, 1, v___x_2749_);
                            v___x_2751_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__6(v___x_2750_, v___y_2726_, v___y_2727_);
                            return v___x_2751_;
                        }
                    }
                }
            }
            2 => {
                v___x_2738_ = crate::leanh::lean_box(0);
                if v_isShared_2736_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2735_, 0, v___x_2738_);
                    v___x_2740_ = v___x_2735_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
                    v___x_2740_ = v_reuseFailAlloc_2741_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3___boxed(
    mut v_id_2753_: *mut crate::leanh::LeanObject,
    mut v___y_2754_: *mut crate::leanh::LeanObject,
    mut v___y_2755_: *mut crate::leanh::LeanObject,
    mut v___y_2756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2757_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_id_2753_, v___y_2754_, v___y_2755_);
    crate::leanh::lean_dec(v___y_2755_);
    crate::leanh::lean_dec_ref(v___y_2754_);
    return v_res_2757_;
}
pub unsafe fn l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(
    mut v_id_2758_: *mut crate::leanh::LeanObject,
    mut v_enableLog_2759_: u8,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2772_: u8 = 0;
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut v_unused_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2789_: u8 = 0;
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2793_: u8 = 0;
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2763_ = lean_st_ref_get(v___y_2761_);
                v_env_2764_ = crate::leanh::lean_ctor_get(v___x_2763_, 0);
                crate::leanh::lean_inc_ref(v_env_2764_);
                crate::leanh::lean_dec(v___x_2763_);
                v_options_2765_ = crate::leanh::lean_ctor_get(v___y_2760_, 2);
                v_currNamespace_2766_ = crate::leanh::lean_ctor_get(v___y_2760_, 6);
                v_openDecls_2767_ = crate::leanh::lean_ctor_get(v___y_2760_, 7);
                v___x_2768_ = lean_st_ref_get(v___y_2761_);
                v_env_2769_ = crate::leanh::lean_ctor_get(v___x_2768_, 0);
                crate::leanh::lean_inc_ref(v_env_2769_);
                crate::leanh::lean_dec(v___x_2768_);
                crate::leanh::lean_inc(v_openDecls_2767_);
                crate::leanh::lean_inc(v_currNamespace_2766_);
                v_res_2770_ = l_Lean_ResolveName_resolveGlobalName(
                    v_env_2764_,
                    v_options_2765_,
                    v_currNamespace_2766_,
                    v_openDecls_2767_,
                    v_id_2758_,
                );
                if v_enableLog_2759_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_2769_);
                    v___x_2771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2771_, 0, v_res_2770_);
                    return v___x_2771_;
                } else {
                    v_isExporting_2772_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_2769_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    crate::leanh::lean_dec_ref(v_env_2769_);
                    if v_isExporting_2772_ == 0 {
                        v___x_2773_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2773_, 0, v_res_2770_);
                        return v___x_2773_;
                    } else {
                        v___x_2774_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__2(v_res_2770_);
                        if crate::leanh::lean_obj_tag(v___x_2774_) == 1 {
                            v_val_2775_ = crate::leanh::lean_ctor_get(v___x_2774_, 0);
                            crate::leanh::lean_inc(v_val_2775_);
                            crate::leanh::lean_dec_ref_known(v___x_2774_, 1);
                            v_fst_2776_ = crate::leanh::lean_ctor_get(v_val_2775_, 0);
                            crate::leanh::lean_inc(v_fst_2776_);
                            crate::leanh::lean_dec(v_val_2775_);
                            v___x_2777_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3(v_fst_2776_, v___y_2760_, v___y_2761_);
                            if crate::leanh::lean_obj_tag(v___x_2777_) == 0 {
                                v_isSharedCheck_2784_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2777_)) as u8;
                                if v_isSharedCheck_2784_ == 0 {
                                    v_unused_2785_ = crate::leanh::lean_ctor_get(v___x_2777_, 0);
                                    crate::leanh::lean_dec(v_unused_2785_);
                                    v___x_2779_ = v___x_2777_;
                                    v_isShared_2780_ = v_isSharedCheck_2784_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2777_);
                                    v___x_2779_ = crate::leanh::lean_box(0);
                                    v_isShared_2780_ = v_isSharedCheck_2784_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_res_2770_);
                                v_a_2786_ = crate::leanh::lean_ctor_get(v___x_2777_, 0);
                                v_isSharedCheck_2793_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2777_)) as u8;
                                if v_isSharedCheck_2793_ == 0 {
                                    v___x_2788_ = v___x_2777_;
                                    v_isShared_2789_ = v_isSharedCheck_2793_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2786_);
                                    crate::leanh::lean_dec(v___x_2777_);
                                    v___x_2788_ = crate::leanh::lean_box(0);
                                    v_isShared_2789_ = v_isSharedCheck_2793_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2774_);
                            v___x_2794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2794_, 0, v_res_2770_);
                            return v___x_2794_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2779_, 0, v_res_2770_);
                    v___x_2782_ = v___x_2779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_res_2770_);
                    v___x_2782_ = v_reuseFailAlloc_2783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2782_;
            }
            3 => {
                if v_isShared_2789_ == 0 {
                    v___x_2791_ = v___x_2788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
                    v___x_2791_ = v_reuseFailAlloc_2792_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1___boxed(
    mut v_id_2795_: *mut crate::leanh::LeanObject,
    mut v_enableLog_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
    mut v___y_2798_: *mut crate::leanh::LeanObject,
    mut v___y_2799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enableLog_boxed_2800_: u8 = 0;
    let mut v_res_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_enableLog_boxed_2800_ = (crate::leanh::lean_unbox(v_enableLog_2796_) as u8);
    v_res_2801_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(
        v_id_2795_,
        v_enableLog_boxed_2800_,
        v___y_2797_,
        v___y_2798_,
    );
    crate::leanh::lean_dec(v___y_2798_);
    crate::leanh::lean_dec_ref(v___y_2797_);
    return v_res_2801_;
}
pub unsafe fn l_Lean_realizeGlobalName(
    mut v_id_2802_: *mut crate::leanh::LeanObject,
    mut v_a_2803_: *mut crate::leanh::LeanObject,
    mut v_a_2804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2806_ = 1;
                crate::leanh::lean_inc(v_id_2802_);
                v___x_2807_ = l_Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1(
                    v_id_2802_,
                    v___x_2806_,
                    v_a_2803_,
                    v_a_2804_,
                );
                if crate::leanh::lean_obj_tag(v___x_2807_) == 0 {
                    v_a_2808_ = crate::leanh::lean_ctor_get(v___x_2807_, 0);
                    crate::leanh::lean_inc(v_a_2808_);
                    crate::leanh::lean_dec_ref_known(v___x_2807_, 1);
                    v___x_2809_ = crate::leanh::lean_box(0);
                    v___x_2810_ = l_List_filterAuxM___at___00Lean_realizeGlobalName_spec__2(
                        v_id_2802_,
                        v_a_2808_,
                        v___x_2809_,
                        v_a_2803_,
                        v_a_2804_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2810_) == 0 {
                        v_a_2811_ = crate::leanh::lean_ctor_get(v___x_2810_, 0);
                        v_isSharedCheck_2819_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2810_)) as u8;
                        if v_isSharedCheck_2819_ == 0 {
                            v___x_2813_ = v___x_2810_;
                            v_isShared_2814_ = v_isSharedCheck_2819_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2811_);
                            crate::leanh::lean_dec(v___x_2810_);
                            v___x_2813_ = crate::leanh::lean_box(0);
                            v_isShared_2814_ = v_isSharedCheck_2819_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2810_;
                    }
                } else {
                    crate::leanh::lean_dec(v_id_2802_);
                    return v___x_2807_;
                }
            }
            1 => {
                v___x_2815_ = l_List_reverse___redArg(v_a_2811_);
                if v_isShared_2814_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2813_, 0, v___x_2815_);
                    v___x_2817_ = v___x_2813_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
                    v___x_2817_ = v_reuseFailAlloc_2818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_realizeGlobalName___boxed(
    mut v_id_2820_: *mut crate::leanh::LeanObject,
    mut v_a_2821_: *mut crate::leanh::LeanObject,
    mut v_a_2822_: *mut crate::leanh::LeanObject,
    mut v_a_2823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2824_ = l_Lean_realizeGlobalName(v_id_2820_, v_a_2821_, v_a_2822_);
    crate::leanh::lean_dec(v_a_2822_);
    crate::leanh::lean_dec_ref(v_a_2821_);
    return v_res_2824_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(
    mut v_opt_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2829_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___redArg(v_opt_2825_, v___y_2826_);
    return v___x_2829_;
}
pub unsafe fn l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5___boxed(
    mut v_opt_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2834_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00Lean_realizeGlobalName_spec__1_spec__3_spec__5(v_opt_2830_, v___y_2831_, v___y_2832_);
    crate::leanh::lean_dec(v___y_2832_);
    crate::leanh::lean_dec_ref(v___y_2831_);
    crate::leanh::lean_dec_ref(v_opt_2830_);
    return v_res_2834_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(
    mut v_a_2835_: *mut crate::leanh::LeanObject,
    mut v_a_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2842_: u8 = 0;
    let mut v_fst_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2835_) == 0 {
                    v___x_2837_ = l_List_reverse___redArg(v_a_2836_);
                    return v___x_2837_;
                } else {
                    v_head_2838_ = crate::leanh::lean_ctor_get(v_a_2835_, 0);
                    v_tail_2839_ = crate::leanh::lean_ctor_get(v_a_2835_, 1);
                    v_isSharedCheck_2848_ = (!crate::leanh::lean_is_exclusive(v_a_2835_)) as u8;
                    if v_isSharedCheck_2848_ == 0 {
                        v___x_2841_ = v_a_2835_;
                        v_isShared_2842_ = v_isSharedCheck_2848_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2839_);
                        crate::leanh::lean_inc(v_head_2838_);
                        crate::leanh::lean_dec(v_a_2835_);
                        v___x_2841_ = crate::leanh::lean_box(0);
                        v_isShared_2842_ = v_isSharedCheck_2848_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2843_ = crate::leanh::lean_ctor_get(v_head_2838_, 0);
                crate::leanh::lean_inc(v_fst_2843_);
                crate::leanh::lean_dec(v_head_2838_);
                if v_isShared_2842_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2841_, 1, v_a_2836_);
                    crate::leanh::lean_ctor_set(v___x_2841_, 0, v_fst_2843_);
                    v___x_2845_ = v___x_2841_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_fst_2843_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_a_2836_);
                    v___x_2845_ = v_reuseFailAlloc_2847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2835_ = v_tail_2839_;
                v_a_2836_ = v___x_2845_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(
    mut v_msg_2849_: *mut crate::leanh::LeanObject,
    mut v___y_2850_: *mut crate::leanh::LeanObject,
    mut v___y_2851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2853_ = crate::leanh::lean_ctor_get(v___y_2850_, 5);
                v___x_2854_ = l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6(v_msg_2849_, v___y_2850_, v___y_2851_);
                v_a_2855_ = crate::leanh::lean_ctor_get(v___x_2854_, 0);
                v_isSharedCheck_2863_ = (!crate::leanh::lean_is_exclusive(v___x_2854_)) as u8;
                if v_isSharedCheck_2863_ == 0 {
                    v___x_2857_ = v___x_2854_;
                    v_isShared_2858_ = v_isSharedCheck_2863_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2855_);
                    crate::leanh::lean_dec(v___x_2854_);
                    v___x_2857_ = crate::leanh::lean_box(0);
                    v_isShared_2858_ = v_isSharedCheck_2863_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2853_);
                v___x_2859_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2859_, 0, v_ref_2853_);
                crate::leanh::lean_ctor_set(v___x_2859_, 1, v_a_2855_);
                if v_isShared_2858_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2857_, 1);
                    crate::leanh::lean_ctor_set(v___x_2857_, 0, v___x_2859_);
                    v___x_2861_ = v___x_2857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
                    v___x_2861_ = v_reuseFailAlloc_2862_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_msg_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2868_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2864_, v___y_2865_, v___y_2866_);
    crate::leanh::lean_dec(v___y_2866_);
    crate::leanh::lean_dec_ref(v___y_2865_);
    return v_res_2868_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_ref_2869_: *mut crate::leanh::LeanObject,
    mut v_msg_2870_: *mut crate::leanh::LeanObject,
    mut v___y_2871_: *mut crate::leanh::LeanObject,
    mut v___y_2872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2886_: u8 = 0;
    let mut v_cancelTk_x3f_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2888_: u8 = 0;
    let mut v_inheritedTraceOptions_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2874_ = crate::leanh::lean_ctor_get(v___y_2871_, 0);
    v_fileMap_2875_ = crate::leanh::lean_ctor_get(v___y_2871_, 1);
    v_options_2876_ = crate::leanh::lean_ctor_get(v___y_2871_, 2);
    v_currRecDepth_2877_ = crate::leanh::lean_ctor_get(v___y_2871_, 3);
    v_maxRecDepth_2878_ = crate::leanh::lean_ctor_get(v___y_2871_, 4);
    v_ref_2879_ = crate::leanh::lean_ctor_get(v___y_2871_, 5);
    v_currNamespace_2880_ = crate::leanh::lean_ctor_get(v___y_2871_, 6);
    v_openDecls_2881_ = crate::leanh::lean_ctor_get(v___y_2871_, 7);
    v_initHeartbeats_2882_ = crate::leanh::lean_ctor_get(v___y_2871_, 8);
    v_maxHeartbeats_2883_ = crate::leanh::lean_ctor_get(v___y_2871_, 9);
    v_quotContext_2884_ = crate::leanh::lean_ctor_get(v___y_2871_, 10);
    v_currMacroScope_2885_ = crate::leanh::lean_ctor_get(v___y_2871_, 11);
    v_diag_2886_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2871_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2887_ = crate::leanh::lean_ctor_get(v___y_2871_, 12);
    v_suppressElabErrors_2888_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2871_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2889_ = crate::leanh::lean_ctor_get(v___y_2871_, 13);
    v_ref_2890_ = l_Lean_replaceRef(v_ref_2869_, v_ref_2879_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2889_);
    crate::leanh::lean_inc(v_cancelTk_x3f_2887_);
    crate::leanh::lean_inc(v_currMacroScope_2885_);
    crate::leanh::lean_inc(v_quotContext_2884_);
    crate::leanh::lean_inc(v_maxHeartbeats_2883_);
    crate::leanh::lean_inc(v_initHeartbeats_2882_);
    crate::leanh::lean_inc(v_openDecls_2881_);
    crate::leanh::lean_inc(v_currNamespace_2880_);
    crate::leanh::lean_inc(v_maxRecDepth_2878_);
    crate::leanh::lean_inc(v_currRecDepth_2877_);
    crate::leanh::lean_inc_ref(v_options_2876_);
    crate::leanh::lean_inc_ref(v_fileMap_2875_);
    crate::leanh::lean_inc_ref(v_fileName_2874_);
    v___x_2891_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2891_, 0, v_fileName_2874_);
    crate::leanh::lean_ctor_set(v___x_2891_, 1, v_fileMap_2875_);
    crate::leanh::lean_ctor_set(v___x_2891_, 2, v_options_2876_);
    crate::leanh::lean_ctor_set(v___x_2891_, 3, v_currRecDepth_2877_);
    crate::leanh::lean_ctor_set(v___x_2891_, 4, v_maxRecDepth_2878_);
    crate::leanh::lean_ctor_set(v___x_2891_, 5, v_ref_2890_);
    crate::leanh::lean_ctor_set(v___x_2891_, 6, v_currNamespace_2880_);
    crate::leanh::lean_ctor_set(v___x_2891_, 7, v_openDecls_2881_);
    crate::leanh::lean_ctor_set(v___x_2891_, 8, v_initHeartbeats_2882_);
    crate::leanh::lean_ctor_set(v___x_2891_, 9, v_maxHeartbeats_2883_);
    crate::leanh::lean_ctor_set(v___x_2891_, 10, v_quotContext_2884_);
    crate::leanh::lean_ctor_set(v___x_2891_, 11, v_currMacroScope_2885_);
    crate::leanh::lean_ctor_set(v___x_2891_, 12, v_cancelTk_x3f_2887_);
    crate::leanh::lean_ctor_set(v___x_2891_, 13, v_inheritedTraceOptions_2889_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2891_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_2886_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2891_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2888_,
    );
    v___x_2892_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_2870_, v___x_2891_, v___y_2872_);
    crate::leanh::lean_dec_ref_known(v___x_2891_, 14);
    return v___x_2892_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_ref_2893_: *mut crate::leanh::LeanObject,
    mut v_msg_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2898_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_2893_, v_msg_2894_, v___y_2895_, v___y_2896_);
    crate::leanh::lean_dec(v___y_2896_);
    crate::leanh::lean_dec_ref(v___y_2895_);
    crate::leanh::lean_dec(v_ref_2893_);
    return v_res_2898_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2900_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0;
    v___x_2901_ = l_Lean_stringToMessageData(v___x_2900_);
    return v___x_2901_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2903_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2;
    v___x_2904_ = l_Lean_stringToMessageData(v___x_2903_);
    return v___x_2904_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2906_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4;
    v___x_2907_ = l_Lean_stringToMessageData(v___x_2906_);
    return v___x_2907_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2909_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6;
    v___x_2910_ = l_Lean_stringToMessageData(v___x_2909_);
    return v___x_2910_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2912_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8;
    v___x_2913_ = l_Lean_stringToMessageData(v___x_2912_);
    return v___x_2913_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2915_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10;
    v___x_2916_ = l_Lean_stringToMessageData(v___x_2915_);
    return v___x_2916_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2918_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12;
    v___x_2919_ = l_Lean_stringToMessageData(v___x_2918_);
    return v___x_2919_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_msg_2920_: *mut crate::leanh::LeanObject,
    mut v_declHint_2921_: *mut crate::leanh::LeanObject,
    mut v___y_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v_isExporting_2927_: u8 = 0;
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: u8 = 0;
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: u8 = 0;
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2981_: u8 = 0;
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2924_ = lean_st_ref_get(v___y_2922_);
                v_env_2925_ = crate::leanh::lean_ctor_get(v___x_2924_, 0);
                crate::leanh::lean_inc_ref(v_env_2925_);
                crate::leanh::lean_dec(v___x_2924_);
                v___x_2926_ = l_Lean_Name_isAnonymous(v_declHint_2921_);
                if v___x_2926_ == 0 {
                    v_isExporting_2927_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_2925_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2927_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_2925_);
                        crate::leanh::lean_dec(v_declHint_2921_);
                        v___x_2928_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2928_, 0, v_msg_2920_);
                        return v___x_2928_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_2925_);
                        v___x_2929_ = l_Lean_Environment_setExporting(v_env_2925_, v___x_2926_);
                        crate::leanh::lean_inc(v_declHint_2921_);
                        crate::leanh::lean_inc_ref(v___x_2929_);
                        v___x_2930_ = l_Lean_Environment_contains(
                            v___x_2929_,
                            v_declHint_2921_,
                            v_isExporting_2927_,
                        );
                        if v___x_2930_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2929_);
                            crate::leanh::lean_dec_ref(v_env_2925_);
                            crate::leanh::lean_dec(v_declHint_2921_);
                            v___x_2931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2931_, 0, v_msg_2920_);
                            return v___x_2931_;
                        } else {
                            v___x_2932_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__2);
                            v___x_2933_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_executeReservedNameAction_spec__3_spec__4_spec__6___closed__5);
                            v___x_2934_ = l_Lean_Options_empty;
                            v___x_2935_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2935_, 0, v___x_2929_);
                            crate::leanh::lean_ctor_set(v___x_2935_, 1, v___x_2932_);
                            crate::leanh::lean_ctor_set(v___x_2935_, 2, v___x_2933_);
                            crate::leanh::lean_ctor_set(v___x_2935_, 3, v___x_2934_);
                            crate::leanh::lean_inc(v_declHint_2921_);
                            v___x_2936_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2921_, v___x_2926_);
                            v_c_2937_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_2937_, 0, v___x_2935_);
                            crate::leanh::lean_ctor_set(v_c_2937_, 1, v___x_2936_);
                            v___x_2938_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2925_,
                                v_declHint_2921_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2938_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_2925_);
                                crate::leanh::lean_dec(v_declHint_2921_);
                                v___x_2939_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
                                v___x_2940_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2940_, 0, v___x_2939_);
                                crate::leanh::lean_ctor_set(v___x_2940_, 1, v_c_2937_);
                                v___x_2941_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
                                v___x_2942_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2942_, 0, v___x_2940_);
                                crate::leanh::lean_ctor_set(v___x_2942_, 1, v___x_2941_);
                                v___x_2943_ = l_Lean_MessageData_note(v___x_2942_);
                                v___x_2944_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2944_, 0, v_msg_2920_);
                                crate::leanh::lean_ctor_set(v___x_2944_, 1, v___x_2943_);
                                v___x_2945_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2945_, 0, v___x_2944_);
                                return v___x_2945_;
                            } else {
                                v_val_2946_ = crate::leanh::lean_ctor_get(v___x_2938_, 0);
                                v_isSharedCheck_2981_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2938_)) as u8;
                                if v_isSharedCheck_2981_ == 0 {
                                    v___x_2948_ = v___x_2938_;
                                    v_isShared_2949_ = v_isSharedCheck_2981_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_2946_);
                                    crate::leanh::lean_dec(v___x_2938_);
                                    v___x_2948_ = crate::leanh::lean_box(0);
                                    v_isShared_2949_ = v_isSharedCheck_2981_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_2925_);
                    crate::leanh::lean_dec(v_declHint_2921_);
                    v___x_2982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2982_, 0, v_msg_2920_);
                    return v___x_2982_;
                }
            }
            1 => {
                v___x_2950_ = crate::leanh::lean_box(0);
                v___x_2951_ = l_Lean_Environment_header(v_env_2925_);
                crate::leanh::lean_dec_ref(v_env_2925_);
                v___x_2952_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2951_);
                v_mod_2953_ = lean_array_get(v___x_2950_, v___x_2952_, v_val_2946_);
                crate::leanh::lean_dec(v_val_2946_);
                crate::leanh::lean_dec_ref(v___x_2952_);
                v___x_2954_ = l_Lean_isPrivateName(v_declHint_2921_);
                crate::leanh::lean_dec(v_declHint_2921_);
                if v___x_2954_ == 0 {
                    v___x_2955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
                    v___x_2956_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2956_, 0, v___x_2955_);
                    crate::leanh::lean_ctor_set(v___x_2956_, 1, v_c_2937_);
                    v___x_2957_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
                    v___x_2958_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2958_, 0, v___x_2956_);
                    crate::leanh::lean_ctor_set(v___x_2958_, 1, v___x_2957_);
                    v___x_2959_ = l_Lean_MessageData_ofName(v_mod_2953_);
                    v___x_2960_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2960_, 0, v___x_2958_);
                    crate::leanh::lean_ctor_set(v___x_2960_, 1, v___x_2959_);
                    v___x_2961_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
                    v___x_2962_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2962_, 0, v___x_2960_);
                    crate::leanh::lean_ctor_set(v___x_2962_, 1, v___x_2961_);
                    v___x_2963_ = l_Lean_MessageData_note(v___x_2962_);
                    v___x_2964_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2964_, 0, v_msg_2920_);
                    crate::leanh::lean_ctor_set(v___x_2964_, 1, v___x_2963_);
                    if v_isShared_2949_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2948_, 0);
                        crate::leanh::lean_ctor_set(v___x_2948_, 0, v___x_2964_);
                        v___x_2966_ = v___x_2948_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
                        v___x_2966_ = v_reuseFailAlloc_2967_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2968_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
                    v___x_2969_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2969_, 0, v___x_2968_);
                    crate::leanh::lean_ctor_set(v___x_2969_, 1, v_c_2937_);
                    v___x_2970_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
                    v___x_2971_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2971_, 0, v___x_2969_);
                    crate::leanh::lean_ctor_set(v___x_2971_, 1, v___x_2970_);
                    v___x_2972_ = l_Lean_MessageData_ofName(v_mod_2953_);
                    v___x_2973_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2973_, 0, v___x_2971_);
                    crate::leanh::lean_ctor_set(v___x_2973_, 1, v___x_2972_);
                    v___x_2974_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
                    v___x_2975_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2975_, 0, v___x_2973_);
                    crate::leanh::lean_ctor_set(v___x_2975_, 1, v___x_2974_);
                    v___x_2976_ = l_Lean_MessageData_note(v___x_2975_);
                    v___x_2977_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2977_, 0, v_msg_2920_);
                    crate::leanh::lean_ctor_set(v___x_2977_, 1, v___x_2976_);
                    if v_isShared_2949_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2948_, 0);
                        crate::leanh::lean_ctor_set(v___x_2948_, 0, v___x_2977_);
                        v___x_2979_ = v___x_2948_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
                        v___x_2979_ = v_reuseFailAlloc_2980_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2966_;
            }
            3 => {
                return v___x_2979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_msg_2983_: *mut crate::leanh::LeanObject,
    mut v_declHint_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2987_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2983_, v_declHint_2984_, v___y_2985_);
    crate::leanh::lean_dec(v___y_2985_);
    return v_res_2987_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(
    mut v_msg_2988_: *mut crate::leanh::LeanObject,
    mut v_declHint_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2993_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_2988_, v_declHint_2989_, v___y_2991_);
                v_a_2994_ = crate::leanh::lean_ctor_get(v___x_2993_, 0);
                v_isSharedCheck_3003_ = (!crate::leanh::lean_is_exclusive(v___x_2993_)) as u8;
                if v_isSharedCheck_3003_ == 0 {
                    v___x_2996_ = v___x_2993_;
                    v_isShared_2997_ = v_isSharedCheck_3003_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2994_);
                    crate::leanh::lean_dec(v___x_2993_);
                    v___x_2996_ = crate::leanh::lean_box(0);
                    v_isShared_2997_ = v_isSharedCheck_3003_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2998_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2999_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2999_, 0, v___x_2998_);
                crate::leanh::lean_ctor_set(v___x_2999_, 1, v_a_2994_);
                if v_isShared_2997_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2996_, 0, v___x_2999_);
                    v___x_3001_ = v___x_2996_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
                    v___x_3001_ = v_reuseFailAlloc_3002_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4___boxed(
    mut v_msg_3004_: *mut crate::leanh::LeanObject,
    mut v_declHint_3005_: *mut crate::leanh::LeanObject,
    mut v___y_3006_: *mut crate::leanh::LeanObject,
    mut v___y_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3009_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_3004_, v_declHint_3005_, v___y_3006_, v___y_3007_);
    crate::leanh::lean_dec(v___y_3007_);
    crate::leanh::lean_dec_ref(v___y_3006_);
    return v_res_3009_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(
    mut v_ref_3010_: *mut crate::leanh::LeanObject,
    mut v_msg_3011_: *mut crate::leanh::LeanObject,
    mut v_declHint_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
    mut v___y_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3016_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4(v_msg_3011_, v_declHint_3012_, v___y_3013_, v___y_3014_);
    v_a_3017_ = crate::leanh::lean_ctor_get(v___x_3016_, 0);
    crate::leanh::lean_inc(v_a_3017_);
    crate::leanh::lean_dec_ref(v___x_3016_);
    v___x_3018_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_3010_, v_a_3017_, v___y_3013_, v___y_3014_);
    return v___x_3018_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg___boxed(
    mut v_ref_3019_: *mut crate::leanh::LeanObject,
    mut v_msg_3020_: *mut crate::leanh::LeanObject,
    mut v_declHint_3021_: *mut crate::leanh::LeanObject,
    mut v___y_3022_: *mut crate::leanh::LeanObject,
    mut v___y_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3025_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_3019_, v_msg_3020_, v_declHint_3021_, v___y_3022_, v___y_3023_);
    crate::leanh::lean_dec(v___y_3023_);
    crate::leanh::lean_dec_ref(v___y_3022_);
    crate::leanh::lean_dec(v_ref_3019_);
    return v_res_3025_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3027_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__0;
    v___x_3028_ = l_Lean_stringToMessageData(v___x_3027_);
    return v___x_3028_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3030_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__2;
    v___x_3031_ = l_Lean_stringToMessageData(v___x_3030_);
    return v___x_3031_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(
    mut v_ref_3032_: *mut crate::leanh::LeanObject,
    mut v_constName_3033_: *mut crate::leanh::LeanObject,
    mut v___y_3034_: *mut crate::leanh::LeanObject,
    mut v___y_3035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: u8 = 0;
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3037_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__1);
    v___x_3038_ = 0;
    crate::leanh::lean_inc(v_constName_3033_);
    v___x_3039_ = l_Lean_MessageData_ofConstName(v_constName_3033_, v___x_3038_);
    v___x_3040_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3040_, 0, v___x_3037_);
    crate::leanh::lean_ctor_set(v___x_3040_, 1, v___x_3039_);
    v___x_3041_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___closed__3);
    v___x_3042_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3042_, 0, v___x_3040_);
    crate::leanh::lean_ctor_set(v___x_3042_, 1, v___x_3041_);
    v___x_3043_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_3032_, v___x_3042_, v_constName_3033_, v___y_3034_, v___y_3035_);
    return v___x_3043_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg___boxed(
    mut v_ref_3044_: *mut crate::leanh::LeanObject,
    mut v_constName_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
    mut v___y_3047_: *mut crate::leanh::LeanObject,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3049_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_3044_, v_constName_3045_, v___y_3046_, v___y_3047_);
    crate::leanh::lean_dec(v___y_3047_);
    crate::leanh::lean_dec_ref(v___y_3046_);
    crate::leanh::lean_dec(v_ref_3044_);
    return v_res_3049_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(
    mut v_a_3050_: *mut crate::leanh::LeanObject,
    mut v_a_3051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3057_: u8 = 0;
    let mut v_snd_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3050_) == 0 {
                    v___x_3052_ = l_List_reverse___redArg(v_a_3051_);
                    return v___x_3052_;
                } else {
                    v_head_3053_ = crate::leanh::lean_ctor_get(v_a_3050_, 0);
                    v_tail_3054_ = crate::leanh::lean_ctor_get(v_a_3050_, 1);
                    v_isSharedCheck_3065_ = (!crate::leanh::lean_is_exclusive(v_a_3050_)) as u8;
                    if v_isSharedCheck_3065_ == 0 {
                        v___x_3056_ = v_a_3050_;
                        v_isShared_3057_ = v_isSharedCheck_3065_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3054_);
                        crate::leanh::lean_inc(v_head_3053_);
                        crate::leanh::lean_dec(v_a_3050_);
                        v___x_3056_ = crate::leanh::lean_box(0);
                        v_isShared_3057_ = v_isSharedCheck_3065_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3058_ = crate::leanh::lean_ctor_get(v_head_3053_, 1);
                v___x_3059_ = l_List_isEmpty___redArg(v_snd_3058_);
                if v___x_3059_ == 0 {
                    crate::leanh::lean_del_object(v___x_3056_);
                    crate::leanh::lean_dec(v_head_3053_);
                    v_a_3050_ = v_tail_3054_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_3057_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3056_, 1, v_a_3051_);
                        v___x_3062_ = v___x_3056_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3064_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_head_3053_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_a_3051_);
                        v___x_3062_ = v_reuseFailAlloc_3064_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_3050_ = v_tail_3054_;
                v_a_3051_ = v___x_3062_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(
    mut v_n_3066_: *mut crate::leanh::LeanObject,
    mut v_cs_3067_: *mut crate::leanh::LeanObject,
    mut v___y_3068_: *mut crate::leanh::LeanObject,
    mut v___y_3069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: u8 = 0;
    let mut v_ref_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3071_ = crate::leanh::lean_box(0);
                v_cs_3072_ = l_List_filterTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__0(v_cs_3067_, v___x_3071_);
                v___x_3076_ = l_List_isEmpty___redArg(v_cs_3072_);
                if v___x_3076_ == 0 {
                    crate::leanh::lean_dec(v_n_3066_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_cs_3072_);
                    v_ref_3077_ = crate::leanh::lean_ctor_get(v___y_3068_, 5);
                    v___x_3078_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_3077_, v_n_3066_, v___y_3068_, v___y_3069_);
                    v_a_3079_ = crate::leanh::lean_ctor_get(v___x_3078_, 0);
                    v_isSharedCheck_3086_ = (!crate::leanh::lean_is_exclusive(v___x_3078_)) as u8;
                    if v_isSharedCheck_3086_ == 0 {
                        v___x_3081_ = v___x_3078_;
                        v_isShared_3082_ = v_isSharedCheck_3086_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3079_);
                        crate::leanh::lean_dec(v___x_3078_);
                        v___x_3081_ = crate::leanh::lean_box(0);
                        v_isShared_3082_ = v_isSharedCheck_3086_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3074_ = l_List_mapTR_loop___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__1(v_cs_3072_, v___x_3071_);
                v___x_3075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3075_, 0, v___x_3074_);
                return v___x_3075_;
            }
            2 => {
                if v_isShared_3082_ == 0 {
                    v___x_3084_ = v___x_3081_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0___boxed(
    mut v_n_3087_: *mut crate::leanh::LeanObject,
    mut v_cs_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3092_ = l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(
        v_n_3087_,
        v_cs_3088_,
        v___y_3089_,
        v___y_3090_,
    );
    crate::leanh::lean_dec(v___y_3090_);
    crate::leanh::lean_dec_ref(v___y_3089_);
    return v_res_3092_;
}
pub unsafe fn l_Lean_realizeGlobalConstCore(
    mut v_n_3093_: *mut crate::leanh::LeanObject,
    mut v_a_3094_: *mut crate::leanh::LeanObject,
    mut v_a_3095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3103_: u8 = 0;
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_n_3093_);
                v___x_3097_ = l_Lean_realizeGlobalName(v_n_3093_, v_a_3094_, v_a_3095_);
                if crate::leanh::lean_obj_tag(v___x_3097_) == 0 {
                    v_a_3098_ = crate::leanh::lean_ctor_get(v___x_3097_, 0);
                    crate::leanh::lean_inc(v_a_3098_);
                    crate::leanh::lean_dec_ref_known(v___x_3097_, 1);
                    v___x_3099_ =
                        l_Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0(
                            v_n_3093_, v_a_3098_, v_a_3094_, v_a_3095_,
                        );
                    return v___x_3099_;
                } else {
                    crate::leanh::lean_dec(v_n_3093_);
                    v_a_3100_ = crate::leanh::lean_ctor_get(v___x_3097_, 0);
                    v_isSharedCheck_3107_ = (!crate::leanh::lean_is_exclusive(v___x_3097_)) as u8;
                    if v_isSharedCheck_3107_ == 0 {
                        v___x_3102_ = v___x_3097_;
                        v_isShared_3103_ = v_isSharedCheck_3107_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3100_);
                        crate::leanh::lean_dec(v___x_3097_);
                        v___x_3102_ = crate::leanh::lean_box(0);
                        v_isShared_3103_ = v_isSharedCheck_3107_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3103_ == 0 {
                    v___x_3105_ = v___x_3102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
                    v___x_3105_ = v_reuseFailAlloc_3106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_realizeGlobalConstCore___boxed(
    mut v_n_3108_: *mut crate::leanh::LeanObject,
    mut v_a_3109_: *mut crate::leanh::LeanObject,
    mut v_a_3110_: *mut crate::leanh::LeanObject,
    mut v_a_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3112_ = l_Lean_realizeGlobalConstCore(v_n_3108_, v_a_3109_, v_a_3110_);
    crate::leanh::lean_dec(v_a_3110_);
    crate::leanh::lean_dec_ref(v_a_3109_);
    return v_res_3112_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(
    mut v_00_u03b1_3113_: *mut crate::leanh::LeanObject,
    mut v_ref_3114_: *mut crate::leanh::LeanObject,
    mut v_constName_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3119_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___redArg(v_ref_3114_, v_constName_3115_, v___y_3116_, v___y_3117_);
    return v___x_3119_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2___boxed(
    mut v_00_u03b1_3120_: *mut crate::leanh::LeanObject,
    mut v_ref_3121_: *mut crate::leanh::LeanObject,
    mut v_constName_3122_: *mut crate::leanh::LeanObject,
    mut v___y_3123_: *mut crate::leanh::LeanObject,
    mut v___y_3124_: *mut crate::leanh::LeanObject,
    mut v___y_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3126_ = l_Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2(v_00_u03b1_3120_, v_ref_3121_, v_constName_3122_, v___y_3123_, v___y_3124_);
    crate::leanh::lean_dec(v___y_3124_);
    crate::leanh::lean_dec_ref(v___y_3123_);
    crate::leanh::lean_dec(v_ref_3121_);
    return v_res_3126_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(
    mut v_00_u03b1_3127_: *mut crate::leanh::LeanObject,
    mut v_ref_3128_: *mut crate::leanh::LeanObject,
    mut v_msg_3129_: *mut crate::leanh::LeanObject,
    mut v_declHint_3130_: *mut crate::leanh::LeanObject,
    mut v___y_3131_: *mut crate::leanh::LeanObject,
    mut v___y_3132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3134_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___redArg(v_ref_3128_, v_msg_3129_, v_declHint_3130_, v___y_3131_, v___y_3132_);
    return v___x_3134_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3___boxed(
    mut v_00_u03b1_3135_: *mut crate::leanh::LeanObject,
    mut v_ref_3136_: *mut crate::leanh::LeanObject,
    mut v_msg_3137_: *mut crate::leanh::LeanObject,
    mut v_declHint_3138_: *mut crate::leanh::LeanObject,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3142_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3(v_00_u03b1_3135_, v_ref_3136_, v_msg_3137_, v_declHint_3138_, v___y_3139_, v___y_3140_);
    crate::leanh::lean_dec(v___y_3140_);
    crate::leanh::lean_dec_ref(v___y_3139_);
    crate::leanh::lean_dec(v_ref_3136_);
    return v_res_3142_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(
    mut v_msg_3143_: *mut crate::leanh::LeanObject,
    mut v_declHint_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3148_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_3143_, v_declHint_3144_, v___y_3146_);
    return v___x_3148_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_msg_3149_: *mut crate::leanh::LeanObject,
    mut v_declHint_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3154_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_3149_, v_declHint_3150_, v___y_3151_, v___y_3152_);
    crate::leanh::lean_dec(v___y_3152_);
    crate::leanh::lean_dec_ref(v___y_3151_);
    return v_res_3154_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b1_3155_: *mut crate::leanh::LeanObject,
    mut v_ref_3156_: *mut crate::leanh::LeanObject,
    mut v_msg_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3161_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_3156_, v_msg_3157_, v___y_3158_, v___y_3159_);
    return v___x_3161_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_3162_: *mut crate::leanh::LeanObject,
    mut v_ref_3163_: *mut crate::leanh::LeanObject,
    mut v_msg_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3168_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_3162_, v_ref_3163_, v_msg_3164_, v___y_3165_, v___y_3166_);
    crate::leanh::lean_dec(v___y_3166_);
    crate::leanh::lean_dec_ref(v___y_3165_);
    crate::leanh::lean_dec(v_ref_3163_);
    return v_res_3168_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(
    mut v_00_u03b1_3169_: *mut crate::leanh::LeanObject,
    mut v_msg_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3174_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_3170_, v___y_3171_, v___y_3172_);
    return v___x_3174_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_00_u03b1_3175_: *mut crate::leanh::LeanObject,
    mut v_msg_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
    mut v___y_3179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3180_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_3175_, v_msg_3176_, v___y_3177_, v___y_3178_);
    crate::leanh::lean_dec(v___y_3178_);
    crate::leanh::lean_dec_ref(v___y_3177_);
    return v_res_3180_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(
    mut v_a_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3181_) == 0 {
                    v___x_3183_ = l_List_reverse___redArg(v_a_3182_);
                    return v___x_3183_;
                } else {
                    v_head_3184_ = crate::leanh::lean_ctor_get(v_a_3181_, 0);
                    v_tail_3185_ = crate::leanh::lean_ctor_get(v_a_3181_, 1);
                    v_isSharedCheck_3194_ = (!crate::leanh::lean_is_exclusive(v_a_3181_)) as u8;
                    if v_isSharedCheck_3194_ == 0 {
                        v___x_3187_ = v_a_3181_;
                        v_isShared_3188_ = v_isSharedCheck_3194_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3185_);
                        crate::leanh::lean_inc(v_head_3184_);
                        crate::leanh::lean_dec(v_a_3181_);
                        v___x_3187_ = crate::leanh::lean_box(0);
                        v_isShared_3188_ = v_isSharedCheck_3194_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3189_ = l_Lean_MessageData_ofExpr(v_head_3184_);
                if v_isShared_3188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3187_, 1, v_a_3182_);
                    crate::leanh::lean_ctor_set(v___x_3187_, 0, v___x_3189_);
                    v___x_3191_ = v___x_3187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_a_3182_);
                    v___x_3191_ = v_reuseFailAlloc_3193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3181_ = v_tail_3185_;
                v_a_3182_ = v___x_3191_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(
    mut v_a_3195_: *mut crate::leanh::LeanObject,
    mut v_a_3196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3202_: u8 = 0;
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3195_) == 0 {
                    v___x_3197_ = l_List_reverse___redArg(v_a_3196_);
                    return v___x_3197_;
                } else {
                    v_head_3198_ = crate::leanh::lean_ctor_get(v_a_3195_, 0);
                    v_tail_3199_ = crate::leanh::lean_ctor_get(v_a_3195_, 1);
                    v_isSharedCheck_3209_ = (!crate::leanh::lean_is_exclusive(v_a_3195_)) as u8;
                    if v_isSharedCheck_3209_ == 0 {
                        v___x_3201_ = v_a_3195_;
                        v_isShared_3202_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3199_);
                        crate::leanh::lean_inc(v_head_3198_);
                        crate::leanh::lean_dec(v_a_3195_);
                        v___x_3201_ = crate::leanh::lean_box(0);
                        v_isShared_3202_ = v_isSharedCheck_3209_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3203_ = crate::leanh::lean_box(0);
                v___x_3204_ = l_Lean_mkConst(v_head_3198_, v___x_3203_);
                if v_isShared_3202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3201_, 1, v_a_3196_);
                    crate::leanh::lean_ctor_set(v___x_3201_, 0, v___x_3204_);
                    v___x_3206_ = v___x_3201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_a_3196_);
                    v___x_3206_ = v_reuseFailAlloc_3208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3195_ = v_tail_3199_;
                v_a_3196_ = v___x_3206_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3211_ =
        l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__0;
    v___x_3212_ = l_Lean_stringToMessageData(v___x_3211_);
    return v___x_3212_;
}
pub unsafe fn _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3214_ =
        l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__2;
    v___x_3215_ = l_Lean_stringToMessageData(v___x_3214_);
    return v___x_3215_;
}
pub unsafe fn l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(
    mut v_n_3216_: *mut crate::leanh::LeanObject,
    mut v_cs_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
    mut v___y_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_cs_3217_) == 1 {
                    v_tail_3233_ = crate::leanh::lean_ctor_get(v_cs_3217_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_3233_) == 0 {
                        crate::leanh::lean_dec(v_n_3216_);
                        v_head_3234_ = crate::leanh::lean_ctor_get(v_cs_3217_, 0);
                        crate::leanh::lean_inc(v_head_3234_);
                        crate::leanh::lean_dec_ref_known(v_cs_3217_, 2);
                        v___x_3235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3235_, 0, v_head_3234_);
                        return v___x_3235_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3222_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1_once), _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__1);
                v___x_3223_ = l_Lean_MessageData_ofName(v_n_3216_);
                v___x_3224_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3224_, 0, v___x_3222_);
                crate::leanh::lean_ctor_set(v___x_3224_, 1, v___x_3223_);
                v___x_3225_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3_once), _init_l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___closed__3);
                v___x_3226_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3226_, 0, v___x_3224_);
                crate::leanh::lean_ctor_set(v___x_3226_, 1, v___x_3225_);
                v___x_3227_ = crate::leanh::lean_box(0);
                v___x_3228_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_3217_, v___x_3227_);
                v___x_3229_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(v___x_3228_, v___x_3227_);
                v___x_3230_ = l_Lean_MessageData_ofList(v___x_3229_);
                v___x_3231_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3231_, 0, v___x_3226_);
                crate::leanh::lean_ctor_set(v___x_3231_, 1, v___x_3230_);
                v___x_3232_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3231_, v___y_3218_, v___y_3219_);
                return v___x_3232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0___boxed(
    mut v_n_3236_: *mut crate::leanh::LeanObject,
    mut v_cs_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3241_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(
        v_n_3236_,
        v_cs_3237_,
        v___y_3238_,
        v___y_3239_,
    );
    crate::leanh::lean_dec(v___y_3239_);
    crate::leanh::lean_dec_ref(v___y_3238_);
    return v_res_3241_;
}
pub unsafe fn l_Lean_realizeGlobalConstNoOverloadCore(
    mut v_n_3242_: *mut crate::leanh::LeanObject,
    mut v_a_3243_: *mut crate::leanh::LeanObject,
    mut v_a_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_n_3242_);
                v___x_3246_ = l_Lean_realizeGlobalConstCore(v_n_3242_, v_a_3243_, v_a_3244_);
                if crate::leanh::lean_obj_tag(v___x_3246_) == 0 {
                    v_a_3247_ = crate::leanh::lean_ctor_get(v___x_3246_, 0);
                    crate::leanh::lean_inc(v_a_3247_);
                    crate::leanh::lean_dec_ref_known(v___x_3246_, 1);
                    v___x_3248_ = l_Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0(v_n_3242_, v_a_3247_, v_a_3243_, v_a_3244_);
                    return v___x_3248_;
                } else {
                    crate::leanh::lean_dec(v_n_3242_);
                    v_a_3249_ = crate::leanh::lean_ctor_get(v___x_3246_, 0);
                    v_isSharedCheck_3256_ = (!crate::leanh::lean_is_exclusive(v___x_3246_)) as u8;
                    if v_isSharedCheck_3256_ == 0 {
                        v___x_3251_ = v___x_3246_;
                        v_isShared_3252_ = v_isSharedCheck_3256_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3249_);
                        crate::leanh::lean_dec(v___x_3246_);
                        v___x_3251_ = crate::leanh::lean_box(0);
                        v_isShared_3252_ = v_isSharedCheck_3256_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3252_ == 0 {
                    v___x_3254_ = v___x_3251_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
                    v___x_3254_ = v_reuseFailAlloc_3255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_realizeGlobalConstNoOverloadCore___boxed(
    mut v_n_3257_: *mut crate::leanh::LeanObject,
    mut v_a_3258_: *mut crate::leanh::LeanObject,
    mut v_a_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3261_ = l_Lean_realizeGlobalConstNoOverloadCore(v_n_3257_, v_a_3258_, v_a_3259_);
    crate::leanh::lean_dec(v_a_3259_);
    crate::leanh::lean_dec_ref(v_a_3258_);
    return v_res_3261_;
}
pub unsafe fn l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(
    mut v_a_3262_: *mut crate::leanh::LeanObject,
    mut v_a_3263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3262_) == 0 {
                    v___x_3264_ = lean_array_to_list(v_a_3263_);
                    return v___x_3264_;
                } else {
                    v_head_3265_ = crate::leanh::lean_ctor_get(v_a_3262_, 0);
                    if crate::leanh::lean_obj_tag(v_head_3265_) == 1 {
                        v_fields_3266_ = crate::leanh::lean_ctor_get(v_head_3265_, 1);
                        if crate::leanh::lean_obj_tag(v_fields_3266_) == 0 {
                            crate::leanh::lean_inc_ref(v_head_3265_);
                            v_tail_3267_ = crate::leanh::lean_ctor_get(v_a_3262_, 1);
                            crate::leanh::lean_inc(v_tail_3267_);
                            crate::leanh::lean_dec_ref_known(v_a_3262_, 2);
                            v_n_3268_ = crate::leanh::lean_ctor_get(v_head_3265_, 0);
                            crate::leanh::lean_inc(v_n_3268_);
                            crate::leanh::lean_dec_ref_known(v_head_3265_, 2);
                            v___x_3269_ = lean_array_push(v_a_3263_, v_n_3268_);
                            v_a_3262_ = v_tail_3267_;
                            v_a_3263_ = v___x_3269_;
                            state = 0;
                            continue;
                        } else {
                            v_tail_3271_ = crate::leanh::lean_ctor_get(v_a_3262_, 1);
                            crate::leanh::lean_inc(v_tail_3271_);
                            crate::leanh::lean_dec_ref_known(v_a_3262_, 2);
                            v_a_3262_ = v_tail_3271_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_tail_3273_ = crate::leanh::lean_ctor_get(v_a_3262_, 1);
                        crate::leanh::lean_inc(v_tail_3273_);
                        crate::leanh::lean_dec_ref_known(v_a_3262_, 2);
                        v_a_3262_ = v_tail_3273_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3280_ =
        l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__2;
    v___x_3281_ = l_Lean_MessageData_ofFormat(v___x_3280_);
    return v___x_3281_;
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(
    mut v_stx_3282_: *mut crate::leanh::LeanObject,
    mut v_k_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
    mut v___y_3285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_stx_3282_) == 3 {
        let mut v_val_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_preresolved_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pre_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3291_: u8 = 0;
        v_val_3287_ = crate::leanh::lean_ctor_get(v_stx_3282_, 2);
        crate::leanh::lean_inc(v_val_3287_);
        v_preresolved_3288_ = crate::leanh::lean_ctor_get(v_stx_3282_, 3);
        v___x_3289_ =
            l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__0;
        crate::leanh::lean_inc(v_preresolved_3288_);
        v_pre_3290_ = l_List_filterMapTR_go___at___00Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0_spec__0(v_preresolved_3288_, v___x_3289_);
        v___x_3291_ = l_List_isEmpty___redArg(v_pre_3290_);
        if v___x_3291_ == 0 {
            let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_val_3287_);
            crate::leanh::lean_dec_ref_known(v_stx_3282_, 4);
            crate::leanh::lean_dec_ref(v_k_3283_);
            v___x_3292_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3292_, 0, v_pre_3290_);
            return v___x_3292_;
        } else {
            let mut v_fileName_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fileMap_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_options_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currRecDepth_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_maxRecDepth_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ref_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currNamespace_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_openDecls_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_initHeartbeats_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_maxHeartbeats_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_quotContext_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_currMacroScope_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_diag_3305_: u8 = 0;
            let mut v_cancelTk_x3f_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_suppressElabErrors_3307_: u8 = 0;
            let mut v_inheritedTraceOptions_3308_: *mut crate::leanh::LeanObject =
                core::ptr::null_mut();
            let mut v_ref_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_pre_3290_);
            v_fileName_3293_ = crate::leanh::lean_ctor_get(v___y_3284_, 0);
            v_fileMap_3294_ = crate::leanh::lean_ctor_get(v___y_3284_, 1);
            v_options_3295_ = crate::leanh::lean_ctor_get(v___y_3284_, 2);
            v_currRecDepth_3296_ = crate::leanh::lean_ctor_get(v___y_3284_, 3);
            v_maxRecDepth_3297_ = crate::leanh::lean_ctor_get(v___y_3284_, 4);
            v_ref_3298_ = crate::leanh::lean_ctor_get(v___y_3284_, 5);
            v_currNamespace_3299_ = crate::leanh::lean_ctor_get(v___y_3284_, 6);
            v_openDecls_3300_ = crate::leanh::lean_ctor_get(v___y_3284_, 7);
            v_initHeartbeats_3301_ = crate::leanh::lean_ctor_get(v___y_3284_, 8);
            v_maxHeartbeats_3302_ = crate::leanh::lean_ctor_get(v___y_3284_, 9);
            v_quotContext_3303_ = crate::leanh::lean_ctor_get(v___y_3284_, 10);
            v_currMacroScope_3304_ = crate::leanh::lean_ctor_get(v___y_3284_, 11);
            v_diag_3305_ = crate::leanh::lean_ctor_get_uint8(
                v___y_3284_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
            );
            v_cancelTk_x3f_3306_ = crate::leanh::lean_ctor_get(v___y_3284_, 12);
            v_suppressElabErrors_3307_ = crate::leanh::lean_ctor_get_uint8(
                v___y_3284_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
            );
            v_inheritedTraceOptions_3308_ = crate::leanh::lean_ctor_get(v___y_3284_, 13);
            v_ref_3309_ = l_Lean_replaceRef(v_stx_3282_, v_ref_3298_);
            crate::leanh::lean_dec_ref_known(v_stx_3282_, 4);
            crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3308_);
            crate::leanh::lean_inc(v_cancelTk_x3f_3306_);
            crate::leanh::lean_inc(v_currMacroScope_3304_);
            crate::leanh::lean_inc(v_quotContext_3303_);
            crate::leanh::lean_inc(v_maxHeartbeats_3302_);
            crate::leanh::lean_inc(v_initHeartbeats_3301_);
            crate::leanh::lean_inc(v_openDecls_3300_);
            crate::leanh::lean_inc(v_currNamespace_3299_);
            crate::leanh::lean_inc(v_maxRecDepth_3297_);
            crate::leanh::lean_inc(v_currRecDepth_3296_);
            crate::leanh::lean_inc_ref(v_options_3295_);
            crate::leanh::lean_inc_ref(v_fileMap_3294_);
            crate::leanh::lean_inc_ref(v_fileName_3293_);
            v___x_3310_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
            crate::leanh::lean_ctor_set(v___x_3310_, 0, v_fileName_3293_);
            crate::leanh::lean_ctor_set(v___x_3310_, 1, v_fileMap_3294_);
            crate::leanh::lean_ctor_set(v___x_3310_, 2, v_options_3295_);
            crate::leanh::lean_ctor_set(v___x_3310_, 3, v_currRecDepth_3296_);
            crate::leanh::lean_ctor_set(v___x_3310_, 4, v_maxRecDepth_3297_);
            crate::leanh::lean_ctor_set(v___x_3310_, 5, v_ref_3309_);
            crate::leanh::lean_ctor_set(v___x_3310_, 6, v_currNamespace_3299_);
            crate::leanh::lean_ctor_set(v___x_3310_, 7, v_openDecls_3300_);
            crate::leanh::lean_ctor_set(v___x_3310_, 8, v_initHeartbeats_3301_);
            crate::leanh::lean_ctor_set(v___x_3310_, 9, v_maxHeartbeats_3302_);
            crate::leanh::lean_ctor_set(v___x_3310_, 10, v_quotContext_3303_);
            crate::leanh::lean_ctor_set(v___x_3310_, 11, v_currMacroScope_3304_);
            crate::leanh::lean_ctor_set(v___x_3310_, 12, v_cancelTk_x3f_3306_);
            crate::leanh::lean_ctor_set(v___x_3310_, 13, v_inheritedTraceOptions_3308_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_3310_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                v_diag_3305_,
            );
            crate::leanh::lean_ctor_set_uint8(
                v___x_3310_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                v_suppressElabErrors_3307_,
            );
            crate::leanh::lean_inc(v___y_3285_);
            v___x_3311_ = crate::leanh::lean_apply_4(
                v_k_3283_,
                v_val_3287_,
                v___x_3310_,
                v___y_3285_,
                crate::leanh::lean_box(0),
            );
            return v___x_3311_;
        }
    } else {
        let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_3283_);
        v___x_3312_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3_once), _init_l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___closed__3);
        v___x_3313_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_stx_3282_, v___x_3312_, v___y_3284_, v___y_3285_);
        crate::leanh::lean_dec(v_stx_3282_);
        return v___x_3313_;
    }
}
pub unsafe fn l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0___boxed(
    mut v_stx_3314_: *mut crate::leanh::LeanObject,
    mut v_k_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
    mut v___y_3318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3319_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(
        v_stx_3314_,
        v_k_3315_,
        v___y_3316_,
        v___y_3317_,
    );
    crate::leanh::lean_dec(v___y_3317_);
    crate::leanh::lean_dec_ref(v___y_3316_);
    return v_res_3319_;
}
pub unsafe fn l_Lean_realizeGlobalConst(
    mut v_stx_3321_: *mut crate::leanh::LeanObject,
    mut v_a_3322_: *mut crate::leanh::LeanObject,
    mut v_a_3323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3337_: u8 = 0;
    let mut v_cancelTk_x3f_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3339_: u8 = 0;
    let mut v_inheritedTraceOptions_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3325_ = crate::leanh::lean_ctor_get(v_a_3322_, 0);
    v_fileMap_3326_ = crate::leanh::lean_ctor_get(v_a_3322_, 1);
    v_options_3327_ = crate::leanh::lean_ctor_get(v_a_3322_, 2);
    v_currRecDepth_3328_ = crate::leanh::lean_ctor_get(v_a_3322_, 3);
    v_maxRecDepth_3329_ = crate::leanh::lean_ctor_get(v_a_3322_, 4);
    v_ref_3330_ = crate::leanh::lean_ctor_get(v_a_3322_, 5);
    v_currNamespace_3331_ = crate::leanh::lean_ctor_get(v_a_3322_, 6);
    v_openDecls_3332_ = crate::leanh::lean_ctor_get(v_a_3322_, 7);
    v_initHeartbeats_3333_ = crate::leanh::lean_ctor_get(v_a_3322_, 8);
    v_maxHeartbeats_3334_ = crate::leanh::lean_ctor_get(v_a_3322_, 9);
    v_quotContext_3335_ = crate::leanh::lean_ctor_get(v_a_3322_, 10);
    v_currMacroScope_3336_ = crate::leanh::lean_ctor_get(v_a_3322_, 11);
    v_diag_3337_ = crate::leanh::lean_ctor_get_uint8(
        v_a_3322_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3338_ = crate::leanh::lean_ctor_get(v_a_3322_, 12);
    v_suppressElabErrors_3339_ = crate::leanh::lean_ctor_get_uint8(
        v_a_3322_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3340_ = crate::leanh::lean_ctor_get(v_a_3322_, 13);
    v___x_3341_ = l_Lean_realizeGlobalConst___closed__0;
    v_ref_3342_ = l_Lean_replaceRef(v_stx_3321_, v_ref_3330_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3340_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3338_);
    crate::leanh::lean_inc(v_currMacroScope_3336_);
    crate::leanh::lean_inc(v_quotContext_3335_);
    crate::leanh::lean_inc(v_maxHeartbeats_3334_);
    crate::leanh::lean_inc(v_initHeartbeats_3333_);
    crate::leanh::lean_inc(v_openDecls_3332_);
    crate::leanh::lean_inc(v_currNamespace_3331_);
    crate::leanh::lean_inc(v_maxRecDepth_3329_);
    crate::leanh::lean_inc(v_currRecDepth_3328_);
    crate::leanh::lean_inc_ref(v_options_3327_);
    crate::leanh::lean_inc_ref(v_fileMap_3326_);
    crate::leanh::lean_inc_ref(v_fileName_3325_);
    v___x_3343_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3343_, 0, v_fileName_3325_);
    crate::leanh::lean_ctor_set(v___x_3343_, 1, v_fileMap_3326_);
    crate::leanh::lean_ctor_set(v___x_3343_, 2, v_options_3327_);
    crate::leanh::lean_ctor_set(v___x_3343_, 3, v_currRecDepth_3328_);
    crate::leanh::lean_ctor_set(v___x_3343_, 4, v_maxRecDepth_3329_);
    crate::leanh::lean_ctor_set(v___x_3343_, 5, v_ref_3342_);
    crate::leanh::lean_ctor_set(v___x_3343_, 6, v_currNamespace_3331_);
    crate::leanh::lean_ctor_set(v___x_3343_, 7, v_openDecls_3332_);
    crate::leanh::lean_ctor_set(v___x_3343_, 8, v_initHeartbeats_3333_);
    crate::leanh::lean_ctor_set(v___x_3343_, 9, v_maxHeartbeats_3334_);
    crate::leanh::lean_ctor_set(v___x_3343_, 10, v_quotContext_3335_);
    crate::leanh::lean_ctor_set(v___x_3343_, 11, v_currMacroScope_3336_);
    crate::leanh::lean_ctor_set(v___x_3343_, 12, v_cancelTk_x3f_3338_);
    crate::leanh::lean_ctor_set(v___x_3343_, 13, v_inheritedTraceOptions_3340_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3343_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3337_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3343_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3339_,
    );
    v___x_3344_ = l_Lean_preprocessSyntaxAndResolve___at___00Lean_realizeGlobalConst_spec__0(
        v_stx_3321_,
        v___x_3341_,
        v___x_3343_,
        v_a_3323_,
    );
    crate::leanh::lean_dec_ref_known(v___x_3343_, 14);
    return v___x_3344_;
}
pub unsafe fn l_Lean_realizeGlobalConst___boxed(
    mut v_stx_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3349_ = l_Lean_realizeGlobalConst(v_stx_3345_, v_a_3346_, v_a_3347_);
    crate::leanh::lean_dec(v_a_3347_);
    crate::leanh::lean_dec_ref(v_a_3346_);
    return v_res_3349_;
}
pub unsafe fn _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3350_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3350_;
}
pub unsafe fn l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(
    mut v_msg_3353_: *mut crate::leanh::LeanObject,
    mut v___y_3354_: *mut crate::leanh::LeanObject,
    mut v___y_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3362_: u8 = 0;
    let mut v_toFunctor_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v___f_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195__overap_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3388_: u8 = 0;
    let mut v_unused_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3390_: u8 = 0;
    let mut v_unused_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3357_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0_once), _init_l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__0);
                v___x_3358_ = l_StateRefT_x27_instMonad___redArg(v___x_3357_);
                v_toApplicative_3359_ = crate::leanh::lean_ctor_get(v___x_3358_, 0);
                v_isSharedCheck_3390_ = (!crate::leanh::lean_is_exclusive(v___x_3358_)) as u8;
                if v_isSharedCheck_3390_ == 0 {
                    v_unused_3391_ = crate::leanh::lean_ctor_get(v___x_3358_, 1);
                    crate::leanh::lean_dec(v_unused_3391_);
                    v___x_3361_ = v___x_3358_;
                    v_isShared_3362_ = v_isSharedCheck_3390_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3359_);
                    crate::leanh::lean_dec(v___x_3358_);
                    v___x_3361_ = crate::leanh::lean_box(0);
                    v_isShared_3362_ = v_isSharedCheck_3390_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3363_ = crate::leanh::lean_ctor_get(v_toApplicative_3359_, 0);
                v_toSeq_3364_ = crate::leanh::lean_ctor_get(v_toApplicative_3359_, 2);
                v_toSeqLeft_3365_ = crate::leanh::lean_ctor_get(v_toApplicative_3359_, 3);
                v_toSeqRight_3366_ = crate::leanh::lean_ctor_get(v_toApplicative_3359_, 4);
                v_isSharedCheck_3388_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3359_)) as u8;
                if v_isSharedCheck_3388_ == 0 {
                    v_unused_3389_ = crate::leanh::lean_ctor_get(v_toApplicative_3359_, 1);
                    crate::leanh::lean_dec(v_unused_3389_);
                    v___x_3368_ = v_toApplicative_3359_;
                    v_isShared_3369_ = v_isSharedCheck_3388_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3366_);
                    crate::leanh::lean_inc(v_toSeqLeft_3365_);
                    crate::leanh::lean_inc(v_toSeq_3364_);
                    crate::leanh::lean_inc(v_toFunctor_3363_);
                    crate::leanh::lean_dec(v_toApplicative_3359_);
                    v___x_3368_ = crate::leanh::lean_box(0);
                    v_isShared_3369_ = v_isSharedCheck_3388_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3370_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__1;
                v___f_3371_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_3363_);
                v___f_3372_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3372_, 0, v_toFunctor_3363_);
                v___f_3373_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3373_, 0, v_toFunctor_3363_);
                v___x_3374_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3374_, 0, v___f_3372_);
                crate::leanh::lean_ctor_set(v___x_3374_, 1, v___f_3373_);
                v___f_3375_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3375_, 0, v_toSeqRight_3366_);
                v___f_3376_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3376_, 0, v_toSeqLeft_3365_);
                v___f_3377_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3377_, 0, v_toSeq_3364_);
                if v_isShared_3369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3368_, 4, v___f_3375_);
                    crate::leanh::lean_ctor_set(v___x_3368_, 3, v___f_3376_);
                    crate::leanh::lean_ctor_set(v___x_3368_, 2, v___f_3377_);
                    crate::leanh::lean_ctor_set(v___x_3368_, 1, v___f_3370_);
                    crate::leanh::lean_ctor_set(v___x_3368_, 0, v___x_3374_);
                    v___x_3379_ = v___x_3368_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3387_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___f_3370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 2, v___f_3377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 3, v___f_3376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 4, v___f_3375_);
                    v___x_3379_ = v_reuseFailAlloc_3387_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3361_, 1, v___f_3371_);
                    crate::leanh::lean_ctor_set(v___x_3361_, 0, v___x_3379_);
                    v___x_3381_ = v___x_3361_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3386_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 1, v___f_3371_);
                    v___x_3381_ = v_reuseFailAlloc_3386_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3382_ = crate::leanh::lean_box(0);
                v___x_3383_ = l_instInhabitedOfMonad___redArg(v___x_3381_, v___x_3382_);
                v___x_195__overap_3384_ = lean_panic_fn_borrowed(v___x_3383_, v_msg_3353_);
                crate::leanh::lean_dec(v___x_3383_);
                crate::leanh::lean_inc(v___y_3355_);
                crate::leanh::lean_inc_ref(v___y_3354_);
                v___x_3385_ = crate::leanh::lean_apply_3(
                    v___x_195__overap_3384_,
                    v___y_3354_,
                    v___y_3355_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0___boxed(
    mut v_msg_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3396_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v_msg_3392_, v___y_3393_, v___y_3394_);
    crate::leanh::lean_dec(v___y_3394_);
    crate::leanh::lean_dec_ref(v___y_3393_);
    return v_res_3396_;
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(
    mut v_x_3398_: *mut crate::leanh::LeanObject,
    mut v_x_3399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3399_) == 0 {
                    return v_x_3398_;
                } else {
                    v_head_3400_ = crate::leanh::lean_ctor_get(v_x_3399_, 0);
                    v_tail_3401_ = crate::leanh::lean_ctor_get(v_x_3399_, 1);
                    v___x_3402_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___closed__0;
                    v___x_3403_ = lean_string_append(v_x_3398_, v___x_3402_);
                    v___x_3404_ = lean_expr_dbg_to_string(v_head_3400_);
                    v___x_3405_ = lean_string_append(v___x_3403_, v___x_3404_);
                    crate::leanh::lean_dec_ref(v___x_3404_);
                    v_x_3398_ = v___x_3405_;
                    v_x_3399_ = v_tail_3401_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2___boxed(
    mut v_x_3407_: *mut crate::leanh::LeanObject,
    mut v_x_3408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3409_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v_x_3407_, v_x_3408_);
    crate::leanh::lean_dec(v_x_3408_);
    return v_res_3409_;
}
pub unsafe fn l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(
    mut v_x_3413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3413_) == 0 {
        let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3414_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__0;
        return v___x_3414_;
    } else {
        let mut v_tail_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3415_ = crate::leanh::lean_ctor_get(v_x_3413_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3415_) == 0 {
            let mut v_head_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_3416_ = crate::leanh::lean_ctor_get(v_x_3413_, 0);
            v___x_3417_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1;
            v___x_3418_ = lean_expr_dbg_to_string(v_head_3416_);
            v___x_3419_ = lean_string_append(v___x_3417_, v___x_3418_);
            crate::leanh::lean_dec_ref(v___x_3418_);
            v___x_3420_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__2;
            v___x_3421_ = lean_string_append(v___x_3419_, v___x_3420_);
            return v___x_3421_;
        } else {
            let mut v_head_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3427_: u32 = 0;
            let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_3422_ = crate::leanh::lean_ctor_get(v_x_3413_, 0);
            v___x_3423_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___closed__1;
            v___x_3424_ = lean_expr_dbg_to_string(v_head_3422_);
            v___x_3425_ = lean_string_append(v___x_3423_, v___x_3424_);
            crate::leanh::lean_dec_ref(v___x_3424_);
            v___x_3426_ = l_List_foldl___at___00List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1_spec__2(v___x_3425_, v_tail_3415_);
            v___x_3427_ = 93;
            v___x_3428_ = lean_string_push(v___x_3426_, v___x_3427_);
            return v___x_3428_;
        }
    }
}
pub unsafe fn l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1___boxed(
    mut v_x_3429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3430_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v_x_3429_);
    crate::leanh::lean_dec(v_x_3429_);
    return v_res_3430_;
}
pub unsafe fn _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ =
        l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__2;
    v___x_3435_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_3436_ = crate::leanh::lean_unsigned_to_nat(429);
    v___x_3437_ =
        l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__1;
    v___x_3438_ =
        l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__0;
    v___x_3439_ = l_mkPanicMessageWithDecl(
        v___x_3438_,
        v___x_3437_,
        v___x_3436_,
        v___x_3435_,
        v___x_3434_,
    );
    return v___x_3439_;
}
pub unsafe fn l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(
    mut v_id_3442_: *mut crate::leanh::LeanObject,
    mut v_cs_3443_: *mut crate::leanh::LeanObject,
    mut v___y_3444_: *mut crate::leanh::LeanObject,
    mut v___y_3445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_cs_3443_) == 0 {
        let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_id_3442_);
        v___x_3447_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3_once), _init_l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__3);
        v___x_3448_ = l_panic___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__0(v___x_3447_, v___y_3444_, v___y_3445_);
        return v___x_3448_;
    } else {
        let mut v_tail_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_3449_ = crate::leanh::lean_ctor_get(v_cs_3443_, 1);
        if crate::leanh::lean_obj_tag(v_tail_3449_) == 0 {
            let mut v_head_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_id_3442_);
            v_head_3450_ = crate::leanh::lean_ctor_get(v_cs_3443_, 0);
            crate::leanh::lean_inc(v_head_3450_);
            crate::leanh::lean_dec_ref_known(v_cs_3443_, 2);
            v___x_3451_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3451_, 0, v_head_3450_);
            return v___x_3451_;
        } else {
            let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3454_: u8 = 0;
            let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3452_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__4;
            v___x_3453_ = crate::leanh::lean_box(0);
            v___x_3454_ = 0;
            crate::leanh::lean_inc(v_id_3442_);
            v___x_3455_ = l_Lean_Syntax_formatStx(v_id_3442_, v___x_3453_, v___x_3454_);
            v___x_3456_ = l_Std_Format_defWidth;
            v___x_3457_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_3458_ = l_Std_Format_pretty(v___x_3455_, v___x_3456_, v___x_3457_, v___x_3457_);
            v___x_3459_ = lean_string_append(v___x_3452_, v___x_3458_);
            crate::leanh::lean_dec_ref(v___x_3458_);
            v___x_3460_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___closed__5;
            v___x_3461_ = lean_string_append(v___x_3459_, v___x_3460_);
            v___x_3462_ = crate::leanh::lean_box(0);
            v___x_3463_ = l_List_mapTR_loop___at___00Lean_ensureNoOverload___at___00Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__0(v_cs_3443_, v___x_3462_);
            v___x_3464_ = l_List_toString___at___00Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0_spec__1(v___x_3463_);
            crate::leanh::lean_dec(v___x_3463_);
            v___x_3465_ = lean_string_append(v___x_3461_, v___x_3464_);
            crate::leanh::lean_dec_ref(v___x_3464_);
            v___x_3466_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3466_, 0, v___x_3465_);
            v___x_3467_ = l_Lean_MessageData_ofFormat(v___x_3466_);
            v___x_3468_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_filterFieldList___at___00Lean_realizeGlobalConstCore_spec__0_spec__2_spec__3_spec__5___redArg(v_id_3442_, v___x_3467_, v___y_3444_, v___y_3445_);
            crate::leanh::lean_dec(v_id_3442_);
            return v___x_3468_;
        }
    }
}
pub unsafe fn l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0___boxed(
    mut v_id_3469_: *mut crate::leanh::LeanObject,
    mut v_cs_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
    mut v___y_3472_: *mut crate::leanh::LeanObject,
    mut v___y_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3474_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(
        v_id_3469_,
        v_cs_3470_,
        v___y_3471_,
        v___y_3472_,
    );
    crate::leanh::lean_dec(v___y_3472_);
    crate::leanh::lean_dec_ref(v___y_3471_);
    return v_res_3474_;
}
pub unsafe fn l_Lean_realizeGlobalConstNoOverload(
    mut v_id_3475_: *mut crate::leanh::LeanObject,
    mut v_a_3476_: *mut crate::leanh::LeanObject,
    mut v_a_3477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3485_: u8 = 0;
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_id_3475_);
                v___x_3479_ = l_Lean_realizeGlobalConst(v_id_3475_, v_a_3476_, v_a_3477_);
                if crate::leanh::lean_obj_tag(v___x_3479_) == 0 {
                    v_a_3480_ = crate::leanh::lean_ctor_get(v___x_3479_, 0);
                    crate::leanh::lean_inc(v_a_3480_);
                    crate::leanh::lean_dec_ref_known(v___x_3479_, 1);
                    v___x_3481_ = l_Lean_ensureNonAmbiguous___at___00Lean_realizeGlobalConstNoOverload_spec__0(v_id_3475_, v_a_3480_, v_a_3476_, v_a_3477_);
                    return v___x_3481_;
                } else {
                    crate::leanh::lean_dec(v_id_3475_);
                    v_a_3482_ = crate::leanh::lean_ctor_get(v___x_3479_, 0);
                    v_isSharedCheck_3489_ = (!crate::leanh::lean_is_exclusive(v___x_3479_)) as u8;
                    if v_isSharedCheck_3489_ == 0 {
                        v___x_3484_ = v___x_3479_;
                        v_isShared_3485_ = v_isSharedCheck_3489_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3482_);
                        crate::leanh::lean_dec(v___x_3479_);
                        v___x_3484_ = crate::leanh::lean_box(0);
                        v_isShared_3485_ = v_isSharedCheck_3489_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3485_ == 0 {
                    v___x_3487_ = v___x_3484_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_realizeGlobalConstNoOverload___boxed(
    mut v_id_3490_: *mut crate::leanh::LeanObject,
    mut v_a_3491_: *mut crate::leanh::LeanObject,
    mut v_a_3492_: *mut crate::leanh::LeanObject,
    mut v_a_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3494_ = l_Lean_realizeGlobalConstNoOverload(v_id_3490_, v_a_3491_, v_a_3492_);
    crate::leanh::lean_dec(v_a_3492_);
    crate::leanh::lean_dec_ref(v_a_3491_);
    return v_res_3494_;
}
pub unsafe fn _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3526_ = crate::leanh::lean_unsigned_to_nat(3863082579);
    v___x_3527_ = l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__12_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_;
    v___x_3528_ = l_Lean_Name_num___override(v___x_3527_, v___x_3526_);
    return v___x_3528_;
}
pub unsafe fn _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3530_ = l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__14_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_;
    v___x_3531_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once), _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__13_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
    v___x_3532_ = l_Lean_Name_str___override(v___x_3531_, v___x_3530_);
    return v___x_3532_;
}
pub unsafe fn _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3534_ = l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__16_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_;
    v___x_3535_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once), _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__15_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
    v___x_3536_ = l_Lean_Name_str___override(v___x_3535_, v___x_3534_);
    return v___x_3536_;
}
pub unsafe fn _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3537_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3538_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once), _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__17_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
    v___x_3539_ = l_Lean_Name_num___override(v___x_3538_, v___x_3537_);
    return v___x_3539_;
}
pub unsafe fn l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: u8 = 0;
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3541_ = l_Lean_executeReservedNameAction___closed__1;
    v___x_3542_ = 0;
    v___x_3543_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2__once), _init_l___private_Lean_ReservedNameAction_0__Lean_initFn___closed__18_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_);
    v___x_3544_ = l_Lean_registerTraceClass(v___x_3541_, v___x_3542_, v___x_3543_);
    return v___x_3544_;
}
pub unsafe fn l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2____boxed(
    mut v_a_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3546_ = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
    return v_res_3546_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ReservedNameAction(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_2721971034____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_ReservedNameAction_0__Lean_reservedNameActionsRef,
    );
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_ReservedNameAction_0__Lean_initFn_00___x40_Lean_ReservedNameAction_3863082579____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ReservedNameAction(
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
pub unsafe fn initialize_Lean_ReservedNameAction(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ReservedNameAction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ReservedNameAction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_ReservedNameAction(builtin);
}

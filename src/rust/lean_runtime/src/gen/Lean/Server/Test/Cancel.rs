// Lean compiler output
// Module: Lean.Server.Test.Cancel
// Imports: Lean.Elab.Command Lean.Elab.Tactic.Basic Lean.Elab.Command Lean.Elab.Tactic.Basic
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getString;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::CancelToken::{
    l_IO_CancelToken_isSet, l_IO_CancelToken_new, l_IO_CancelToken_set,
};
use crate::r#gen::Init::System::IO::l_IO_sleep;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::System::Promise::l_IO_Promise_result_x21___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_getMessageLog___redArg, l_Lean_Core_instInhabitedCoreM___lam__0___boxed,
    l_Lean_Core_logSnapshotTask___redArg, l_Lean_Core_wrapAsyncAsSnapshot___redArg,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_liftCoreM___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed,
    runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot,
    l_Lean_Elab_Term_instInhabitedTermElabM, l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_interruptExceptionId;
use crate::r#gen::Lean::Language::Basic::{
    l_Lean_Language_Snapshot_Diagnostics_ofMessageLog,
    l_Lean_Language_SnapshotTask_defaultReportingRange,
    l_Lean_Language_instInhabitedSnapshotTask_default___redArg,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed,
    lean_string_dec_eq, lean_string_hash,
};
use crate::lean_imports_rs::Init::System::IO::{lean_get_stderr, lean_io_as_task, lean_io_wait};
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_dbg_trace;
pub static mut l_Lean_Server_Test_Cancel_onceRef: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value:
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
    m_data: [83, 101, 114, 118, 101, 114, 0],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value:
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
    m_data: [84, 101, 115, 116, 0],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value:
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
    m_data: [67, 97, 110, 99, 101, 108, 0],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__4_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101,
        108, 95, 111, 110, 99, 101, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_0:
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
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15371898625421214203 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        550335043767327247 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14272645075865723750 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        12727115358193553860 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__6_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        119, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101,
        0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__7_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [98, 108, 111, 99, 107, 101, 100, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4_value: crate::leanh::LeanStringObject<94> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 93, m_data: [95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 97, 110, 99, 101, 108, 108, 101, 100, 33, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [99, 97, 110, 99, 101, 108, 108, 101, 100, 32, 40, 115, 104, 111, 117, 108, 100, 32, 110, 101, 118, 101, 114, 32, 98, 101, 32, 118, 105, 115, 105, 98, 108, 101, 41, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 84, 101, 115, 116, 46, 67, 97, 110, 99, 101, 108, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11_value: crate::leanh::LeanStringObject<118> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 118, m_capacity: 118, m_length: 117, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 84, 101, 115, 116, 46, 67, 97, 110, 99, 101, 108, 46, 95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 108, 111, 99, 107, 101, 100, 33, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_unblockedCancelTkRef: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 117, 110, 98, 108, 111,
        99, 107, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_0:
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
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15371898625421214203 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        550335043767327247 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14272645075865723750 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16312521998838811843 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__2_value:
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
        119, 97, 105, 116, 95, 102, 111, 114, 95, 117, 110, 98, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<90> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 90, m_capacity: 90, m_length: 89, m_data: [95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 117, 110, 98, 108, 111, 99, 107, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1_value: crate::leanh::LeanStringObject<114> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 114, m_capacity: 114, m_length: 113, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 84, 101, 115, 116, 46, 67, 97, 110, 99, 101, 108, 46, 95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 117, 110, 98, 108, 111, 99, 107, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 117, 110, 98, 108, 111,
        99, 107, 95, 97, 115, 121, 110, 99, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_0:
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
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15371898625421214203 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        550335043767327247 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14272645075865723750 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        1993327346138415696 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__2_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        119, 97, 105, 116, 95, 102, 111, 114, 95, 117, 110, 98, 108, 111, 99, 107, 95, 97, 115,
        121, 110, 99, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__3_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<120> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 120, m_capacity: 120, m_length: 119, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 84, 101, 115, 116, 46, 67, 97, 110, 99, 101, 108, 46, 95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 117, 110, 98, 108, 111, 99, 107, 95, 97, 115, 121, 110, 99, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__1_value: crate::leanh::LeanStringObject<96> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 96, m_capacity: 96, m_length: 95, m_data: [95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 117, 110, 98, 108, 111, 99, 107, 95, 97, 115, 121, 110, 99, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value) as *mut crate::leanh::LeanObject,550335043767327247 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value) as *mut crate::leanh::LeanObject,14272645075865723750 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__1_value) as *mut crate::leanh::LeanObject,14628553986487120063 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel_tacticUnblock___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [116, 97, 99, 116, 105, 99, 85, 110, 98, 108, 111, 99, 107, 0],
};
static mut l_Lean_Server_Test_Cancel_tacticUnblock___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_0:
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
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15371898625421214203 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        550335043767327247 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14272645075865723750 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11719445552797615857 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticUnblock___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticUnblock___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [117, 110, 98, 108, 111, 99, 107, 0],
};
static mut l_Lean_Server_Test_Cancel_tacticUnblock___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticUnblock___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticUnblock___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticUnblock___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticUnblock___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_tacticUnblock: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticUnblock___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0___boxed as *const core::ffi::c_void, m_arity: 10, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 110, 98, 108, 111, 99, 107, 105, 110, 103, 33, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__0_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101,
        108, 95, 111, 110, 99, 101, 95, 97, 115, 121, 110, 99, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_0:
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
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15371898625421214203 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        550335043767327247 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14272645075865723750 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15331508823141302538 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__2_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        119, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101,
        95, 97, 115, 121, 110, 99, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__3_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0_value: crate::leanh::LeanStringObject<124> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 124, m_capacity: 124, m_length: 123, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 84, 101, 115, 116, 46, 67, 97, 110, 99, 101, 108, 46, 95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 97, 115, 121, 110, 99, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0___boxed as *const core::ffi::c_void, m_arity: 10, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__1_value: crate::leanh::LeanStringObject<100> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 100, m_capacity: 100, m_length: 99, m_data: [95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 97, 115, 121, 110, 99, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value) as *mut crate::leanh::LeanObject,550335043767327247 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value) as *mut crate::leanh::LeanObject,14272645075865723750 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__1_value) as *mut crate::leanh::LeanObject,3268625668059462399 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__0_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 109, 97, 105, 110, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 97, 115, 121, 110, 99, 0]};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value) as *mut crate::leanh::LeanObject,550335043767327247 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value) as *mut crate::leanh::LeanObject,14272645075865723750 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__0_value) as *mut crate::leanh::LeanObject,15333701747658016900 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__2_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [119, 97, 105, 116, 95, 102, 111, 114, 95, 109, 97, 105, 110, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 97, 115, 121, 110, 99, 0]};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 6 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__2_value) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1_value) as *mut crate::leanh::LeanObject,((( 1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__0_value: crate::leanh::LeanStringObject<105> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 105, m_capacity: 105, m_length: 104, m_data: [95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 109, 97, 105, 110, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 97, 115, 121, 110, 99, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value) as *mut crate::leanh::LeanObject,550335043767327247 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value) as *mut crate::leanh::LeanObject,14272645075865723750 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__0_value) as *mut crate::leanh::LeanObject,10351670148559056645 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3_value: crate::leanh::LeanStringObject<129> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 129, m_capacity: 129, m_length: 128, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 84, 101, 115, 116, 46, 67, 97, 110, 99, 101, 108, 46, 95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 109, 97, 105, 110, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 97, 115, 121, 110, 99, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_Test_Cancel_cmdOnceRef: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [99, 111, 109, 109, 97, 110, 100, 87, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 99, 111, 109, 109, 97, 110, 100, 95, 0]};
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value) as *mut crate::leanh::LeanObject,15371898625421214203 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value) as *mut crate::leanh::LeanObject,550335043767327247 as *mut crate::leanh::LeanObject] };
static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value) as *mut crate::leanh::LeanObject,14272645075865723750 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__0_value) as *mut crate::leanh::LeanObject,10090950077376423394 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__2_value) as *mut crate::leanh::LeanObject,12571085391447129896 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__4_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [119, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 99, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__6_value) as *mut crate::leanh::LeanObject,6110315075117401315 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 2 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1_value) as *mut crate::leanh::LeanObject,((( 1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__10_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command__:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0_value: crate::leanh::LeanStringObject<104> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 104, m_capacity: 104, m_length: 103, m_data: [95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 99, 111, 109, 109, 97, 110, 100, 87, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 99, 111, 109, 109, 97, 110, 100, 95, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1_value: crate::leanh::LeanStringObject<128> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 128, m_capacity: 128, m_length: 127, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 84, 101, 115, 116, 46, 67, 97, 110, 99, 101, 108, 46, 95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 99, 111, 109, 109, 97, 110, 100, 87, 97, 105, 116, 95, 102, 111, 114, 95, 99, 97, 110, 99, 101, 108, 95, 111, 110, 99, 101, 95, 99, 111, 109, 109, 97, 110, 100, 95, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_Test_Cancel_testTasksRef: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__0_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 116, 101, 115, 116, 95,
        116, 97, 115, 107, 95, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_0:
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
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15371898625421214203 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        550335043767327247 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14272645075865723750 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__0_value
        ) as *mut crate::leanh::LeanObject,
        8841775172197020075 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__2_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        119, 97, 105, 116, 95, 102, 111, 114, 95, 116, 101, 115, 116, 95, 116, 97, 115, 107, 32, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__2_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__4_value:
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
    m_data: [115, 116, 114, 0],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__5_value:
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
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__4_value
        ) as *mut crate::leanh::LeanObject,
        9232979286016572671 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__5_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1_value
        ) as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__7_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__8_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_tacticWait__for__test__task__:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__0_value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [119, 97, 105, 116, 95, 102, 111, 114, 95, 116, 101, 115, 116, 95, 116, 97, 115, 107, 58, 32, 110, 111, 32, 116, 97, 115, 107, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 102, 111, 114, 32, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__1_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [119, 97, 105, 116, 95, 102, 111, 114, 95, 116, 101, 115, 116, 95, 116, 97, 115, 107, 58, 32, 116, 97, 115, 107, 32, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [32, 100, 114, 111, 112, 112, 101, 100, 32, 119, 105, 116, 104, 111, 117, 116, 32, 114, 101, 115, 111, 108, 117, 116, 105, 111, 110, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_syncPromisesRef: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        116, 97, 99, 116, 105, 99, 87, 97, 105, 116, 95, 102, 111, 114, 95, 115, 121, 110, 99, 95,
        0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_0:
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
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15371898625421214203 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        550335043767327247 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14272645075865723750 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        10922142494454896440 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__2_value:
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
        119, 97, 105, 116, 95, 102, 111, 114, 95, 115, 121, 110, 99, 32, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_tacticWait__for__sync__: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___closed__0_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [119, 97, 105, 116, 95, 102, 111, 114, 95, 115, 121, 110, 99, 58, 32, 115, 121, 110, 99, 32, 112, 114, 111, 109, 105, 115, 101, 32, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__0_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        116, 97, 99, 116, 105, 99, 66, 108, 111, 99, 107, 95, 117, 110, 116, 105, 108, 95, 99, 97,
        110, 99, 101, 108, 108, 101, 100, 95, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_0:
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
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15371898625421214203 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        550335043767327247 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14272645075865723750 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__0_value
        ) as *mut crate::leanh::LeanObject,
        10730195490517816953 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__2_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        98, 108, 111, 99, 107, 95, 117, 110, 116, 105, 108, 95, 99, 97, 110, 99, 101, 108, 108,
        101, 100, 0,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 6,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__2_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__3_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__6_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1_value
        ) as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__4_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__5_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled__:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__0_value: crate::leanh::LeanStringObject<120> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 120, m_capacity: 120, m_length: 119, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 84, 101, 115, 116, 46, 67, 97, 110, 99, 101, 108, 46, 95, 97, 117, 120, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 95, 95, 101, 108, 97, 98, 82, 117, 108, 101, 115, 95, 76, 101, 97, 110, 95, 83, 101, 114, 118, 101, 114, 95, 84, 101, 115, 116, 95, 67, 97, 110, 99, 101, 108, 95, 116, 97, 99, 116, 105, 99, 66, 108, 111, 99, 107, 95, 117, 110, 116, 105, 108, 95, 99, 97, 110, 99, 101, 108, 108, 101, 100, 95, 95, 49, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [58, 32, 98, 108, 111, 99, 107, 101, 100, 0]};
static mut l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__2_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2798_ = crate::leanh::lean_box(0);
    v___x_2799_ = lean_st_mk_ref(v___x_2798_);
    v___x_2800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2800_, 0, v___x_2799_);
    return v___x_2800_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2____boxed(
    mut v_a_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2802_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
    return v_res_2802_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2823_ = crate::leanh::lean_box(0);
    v___x_2824_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2825_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2825_, 0, v___x_2824_);
    crate::leanh::lean_ctor_set(v___x_2825_, 1, v___x_2823_);
    return v___x_2825_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0);
    v___x_2828_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2828_, 0, v___x_2827_);
    return v___x_2828_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___boxed(
    mut v___y_2829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2830_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
    return v_res_2830_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0(
    mut v_00_u03b1_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
    return v___x_2841_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___boxed(
    mut v_00_u03b1_2842_: *mut crate::leanh::LeanObject,
    mut v___y_2843_: *mut crate::leanh::LeanObject,
    mut v___y_2844_: *mut crate::leanh::LeanObject,
    mut v___y_2845_: *mut crate::leanh::LeanObject,
    mut v___y_2846_: *mut crate::leanh::LeanObject,
    mut v___y_2847_: *mut crate::leanh::LeanObject,
    mut v___y_2848_: *mut crate::leanh::LeanObject,
    mut v___y_2849_: *mut crate::leanh::LeanObject,
    mut v___y_2850_: *mut crate::leanh::LeanObject,
    mut v___y_2851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0(v_00_u03b1_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
    crate::leanh::lean_dec(v___y_2850_);
    crate::leanh::lean_dec_ref(v___y_2849_);
    crate::leanh::lean_dec(v___y_2848_);
    crate::leanh::lean_dec_ref(v___y_2847_);
    crate::leanh::lean_dec(v___y_2846_);
    crate::leanh::lean_dec_ref(v___y_2845_);
    crate::leanh::lean_dec(v___y_2844_);
    crate::leanh::lean_dec_ref(v___y_2843_);
    return v_res_2852_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2853_ = crate::leanh::lean_box(0);
    v___x_2854_ = l_Lean_interruptExceptionId;
    v___x_2855_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2855_, 0, v___x_2854_);
    crate::leanh::lean_ctor_set(v___x_2855_, 1, v___x_2853_);
    return v___x_2855_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2857_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___closed__0);
    v___x_2858_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2858_, 0, v___x_2857_);
    return v___x_2858_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg___boxed(
    mut v___y_2859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2860_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
    return v_res_2860_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4(
    mut v_00_u03b1_2861_: *mut crate::leanh::LeanObject,
    mut v___y_2862_: *mut crate::leanh::LeanObject,
    mut v___y_2863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2865_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
    return v___x_2865_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___boxed(
    mut v_00_u03b1_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
    mut v___y_2868_: *mut crate::leanh::LeanObject,
    mut v___y_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2870_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4(v_00_u03b1_2866_, v___y_2867_, v___y_2868_);
    crate::leanh::lean_dec(v___y_2868_);
    crate::leanh::lean_dec_ref(v___y_2867_);
    return v_res_2870_;
}
pub unsafe fn l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(
    mut v_msg_2872_: *mut crate::leanh::LeanObject,
    mut v___y_2873_: *mut crate::leanh::LeanObject,
    mut v___y_2874_: *mut crate::leanh::LeanObject,
    mut v___y_2875_: *mut crate::leanh::LeanObject,
    mut v___y_2876_: *mut crate::leanh::LeanObject,
    mut v___y_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10788__overap_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2882_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___closed__0;
    v___x_10788__overap_2883_ = lean_panic_fn_borrowed(v___f_2882_, v_msg_2872_);
    crate::leanh::lean_inc(v___y_2880_);
    crate::leanh::lean_inc_ref(v___y_2879_);
    crate::leanh::lean_inc(v___y_2878_);
    crate::leanh::lean_inc_ref(v___y_2877_);
    crate::leanh::lean_inc(v___y_2876_);
    crate::leanh::lean_inc_ref(v___y_2875_);
    crate::leanh::lean_inc(v___y_2874_);
    crate::leanh::lean_inc_ref(v___y_2873_);
    v___x_2884_ = crate::leanh::lean_apply_9(
        v___x_10788__overap_2883_,
        v___y_2873_,
        v___y_2874_,
        v___y_2875_,
        v___y_2876_,
        v___y_2877_,
        v___y_2878_,
        v___y_2879_,
        v___y_2880_,
        crate::leanh::lean_box(0),
    );
    return v___x_2884_;
}
pub unsafe fn l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5___boxed(
    mut v_msg_2885_: *mut crate::leanh::LeanObject,
    mut v___y_2886_: *mut crate::leanh::LeanObject,
    mut v___y_2887_: *mut crate::leanh::LeanObject,
    mut v___y_2888_: *mut crate::leanh::LeanObject,
    mut v___y_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
    mut v___y_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2895_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v_msg_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
    crate::leanh::lean_dec(v___y_2893_);
    crate::leanh::lean_dec_ref(v___y_2892_);
    crate::leanh::lean_dec(v___y_2891_);
    crate::leanh::lean_dec_ref(v___y_2890_);
    crate::leanh::lean_dec(v___y_2889_);
    crate::leanh::lean_dec_ref(v___y_2888_);
    crate::leanh::lean_dec(v___y_2887_);
    crate::leanh::lean_dec_ref(v___y_2886_);
    return v_res_2895_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(
    mut v_val_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: u32 = 0;
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2898_ = l_IO_CancelToken_isSet(v_val_2896_);
                if v___x_2898_ == 0 {
                    v___x_2899_ = 30;
                    v___x_2900_ = l_IO_sleep(v___x_2899_);
                    state = 0;
                    continue;
                } else {
                    v___x_2902_ = crate::leanh::lean_box(0);
                    v___x_2903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2903_, 0, v___x_2902_);
                    return v___x_2903_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg___boxed(
    mut v_val_2904_: *mut crate::leanh::LeanObject,
    mut v___y_2905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2906_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_2904_);
    crate::leanh::lean_dec_ref(v_val_2904_);
    return v_res_2906_;
}
pub unsafe fn l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(
    mut v_s_2907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2909_ = lean_get_stderr();
    v_putStr_2910_ = crate::leanh::lean_ctor_get(v___x_2909_, 4);
    crate::leanh::lean_inc_ref(v_putStr_2910_);
    crate::leanh::lean_dec_ref(v___x_2909_);
    v___x_2911_ = crate::leanh::lean_apply_2(v_putStr_2910_, v_s_2907_, crate::leanh::lean_box(0));
    return v___x_2911_;
}
pub unsafe fn l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4___boxed(
    mut v_s_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2914_ = l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(v_s_2912_);
    return v_res_2914_;
}
pub unsafe fn l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(
    mut v_s_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2917_: u32 = 0;
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = 10;
    v___x_2918_ = lean_string_push(v_s_2915_, v___x_2917_);
    v___x_2919_ = l_IO_eprint___at___00IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3_spec__4(v___x_2918_);
    return v___x_2919_;
}
pub unsafe fn l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3___boxed(
    mut v_s_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2922_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v_s_2920_);
    return v_res_2922_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(
    mut v_msgData_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
    mut v___y_2925_: *mut crate::leanh::LeanObject,
    mut v___y_2926_: *mut crate::leanh::LeanObject,
    mut v___y_2927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2929_ = lean_st_ref_get(v___y_2927_);
    v_env_2930_ = crate::leanh::lean_ctor_get(v___x_2929_, 0);
    crate::leanh::lean_inc_ref(v_env_2930_);
    crate::leanh::lean_dec(v___x_2929_);
    v___x_2931_ = lean_st_ref_get(v___y_2925_);
    v_mctx_2932_ = crate::leanh::lean_ctor_get(v___x_2931_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2932_);
    crate::leanh::lean_dec(v___x_2931_);
    v_lctx_2933_ = crate::leanh::lean_ctor_get(v___y_2924_, 2);
    v_options_2934_ = crate::leanh::lean_ctor_get(v___y_2926_, 2);
    crate::leanh::lean_inc_ref(v_options_2934_);
    crate::leanh::lean_inc_ref(v_lctx_2933_);
    v___x_2935_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2935_, 0, v_env_2930_);
    crate::leanh::lean_ctor_set(v___x_2935_, 1, v_mctx_2932_);
    crate::leanh::lean_ctor_set(v___x_2935_, 2, v_lctx_2933_);
    crate::leanh::lean_ctor_set(v___x_2935_, 3, v_options_2934_);
    v___x_2936_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2936_, 0, v___x_2935_);
    crate::leanh::lean_ctor_set(v___x_2936_, 1, v_msgData_2923_);
    v___x_2937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2937_, 0, v___x_2936_);
    return v___x_2937_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4___boxed(
    mut v_msgData_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
    mut v___y_2940_: *mut crate::leanh::LeanObject,
    mut v___y_2941_: *mut crate::leanh::LeanObject,
    mut v___y_2942_: *mut crate::leanh::LeanObject,
    mut v___y_2943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2944_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v_msgData_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
    crate::leanh::lean_dec(v___y_2942_);
    crate::leanh::lean_dec_ref(v___y_2941_);
    crate::leanh::lean_dec(v___y_2940_);
    crate::leanh::lean_dec_ref(v___y_2939_);
    return v_res_2944_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(
    mut v_opts_2945_: *mut crate::leanh::LeanObject,
    mut v_opt_2946_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2947_ = crate::leanh::lean_ctor_get(v_opt_2946_, 0);
    v_defValue_2948_ = crate::leanh::lean_ctor_get(v_opt_2946_, 1);
    v_map_2949_ = crate::leanh::lean_ctor_get(v_opts_2945_, 0);
    v___x_2950_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2949_,
            v_name_2947_,
        );
    if crate::leanh::lean_obj_tag(v___x_2950_) == 0 {
        let mut v___x_2951_: u8 = 0;
        v___x_2951_ = (crate::leanh::lean_unbox(v_defValue_2948_) as u8);
        return v___x_2951_;
    } else {
        let mut v_val_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2952_ = crate::leanh::lean_ctor_get(v___x_2950_, 0);
        crate::leanh::lean_inc(v_val_2952_);
        crate::leanh::lean_dec_ref_known(v___x_2950_, 1);
        if crate::leanh::lean_obj_tag(v_val_2952_) == 1 {
            let mut v_v_2953_: u8 = 0;
            v_v_2953_ = crate::leanh::lean_ctor_get_uint8(v_val_2952_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2952_, 0);
            return v_v_2953_;
        } else {
            let mut v___x_2954_: u8 = 0;
            crate::leanh::lean_dec(v_val_2952_);
            v___x_2954_ = (crate::leanh::lean_unbox(v_defValue_2948_) as u8);
            return v___x_2954_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5___boxed(
    mut v_opts_2955_: *mut crate::leanh::LeanObject,
    mut v_opt_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2957_: u8 = 0;
    let mut v_r_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2957_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_opts_2955_, v_opt_2956_);
    crate::leanh::lean_dec_ref(v_opt_2956_);
    crate::leanh::lean_dec_ref(v_opts_2955_);
    v_r_2958_ = crate::leanh::lean_box((v_res_2957_) as usize);
    return v_r_2958_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(
    mut v___y_2967_: u8,
    mut v_suppressElabErrors_2968_: u8,
    mut v_x_2969_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2969_) == 1 {
        let mut v_pre_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2970_ = crate::leanh::lean_ctor_get(v_x_2969_, 0);
        match crate::leanh::lean_obj_tag(v_pre_2970_) {
            1 => {
                let mut v_pre_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_2971_ = crate::leanh::lean_ctor_get(v_pre_2970_, 0);
                match crate::leanh::lean_obj_tag(v_pre_2971_) {
                    0 => {
                        let mut v_str_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2975_: u8 = 0;
                        v_str_2972_ = crate::leanh::lean_ctor_get(v_x_2969_, 1);
                        v_str_2973_ = crate::leanh::lean_ctor_get(v_pre_2970_, 1);
                        v___x_2974_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__0;
                        v___x_2975_ = lean_string_dec_eq(v_str_2973_, v___x_2974_);
                        if v___x_2975_ == 0 {
                            let mut v___x_2976_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2977_: u8 = 0;
                            v___x_2976_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__1;
                            v___x_2977_ = lean_string_dec_eq(v_str_2973_, v___x_2976_);
                            if v___x_2977_ == 0 {
                                return v___y_2967_;
                            } else {
                                let mut v___x_2978_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2979_: u8 = 0;
                                v___x_2978_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__2;
                                v___x_2979_ = lean_string_dec_eq(v_str_2972_, v___x_2978_);
                                if v___x_2979_ == 0 {
                                    return v___y_2967_;
                                } else {
                                    return v_suppressElabErrors_2968_;
                                }
                            }
                        } else {
                            let mut v___x_2980_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2981_: u8 = 0;
                            v___x_2980_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__3;
                            v___x_2981_ = lean_string_dec_eq(v_str_2972_, v___x_2980_);
                            if v___x_2981_ == 0 {
                                return v___y_2967_;
                            } else {
                                return v_suppressElabErrors_2968_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2982_ = crate::leanh::lean_ctor_get(v_pre_2971_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_2982_) == 0 {
                            let mut v_str_2983_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2984_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2985_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2986_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2987_: u8 = 0;
                            v_str_2983_ = crate::leanh::lean_ctor_get(v_x_2969_, 1);
                            v_str_2984_ = crate::leanh::lean_ctor_get(v_pre_2970_, 1);
                            v_str_2985_ = crate::leanh::lean_ctor_get(v_pre_2971_, 1);
                            v___x_2986_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__4;
                            v___x_2987_ = lean_string_dec_eq(v_str_2985_, v___x_2986_);
                            if v___x_2987_ == 0 {
                                return v___y_2967_;
                            } else {
                                let mut v___x_2988_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2989_: u8 = 0;
                                v___x_2988_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__5;
                                v___x_2989_ = lean_string_dec_eq(v_str_2984_, v___x_2988_);
                                if v___x_2989_ == 0 {
                                    return v___y_2967_;
                                } else {
                                    let mut v___x_2990_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2991_: u8 = 0;
                                    v___x_2990_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__6;
                                    v___x_2991_ = lean_string_dec_eq(v_str_2983_, v___x_2990_);
                                    if v___x_2991_ == 0 {
                                        return v___y_2967_;
                                    } else {
                                        return v_suppressElabErrors_2968_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2967_;
                        }
                    }
                    _ => {
                        return v___y_2967_;
                    }
                }
            }
            0 => {
                let mut v_str_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2994_: u8 = 0;
                v_str_2992_ = crate::leanh::lean_ctor_get(v_x_2969_, 1);
                v___x_2993_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___closed__7;
                v___x_2994_ = lean_string_dec_eq(v_str_2992_, v___x_2993_);
                if v___x_2994_ == 0 {
                    return v___y_2967_;
                } else {
                    return v_suppressElabErrors_2968_;
                }
            }
            _ => {
                return v___y_2967_;
            }
        }
    } else {
        return v___y_2967_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed(
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_2996_: *mut crate::leanh::LeanObject,
    mut v_x_2997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_14940__boxed_2998_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2999_: u8 = 0;
    let mut v_res_3000_: u8 = 0;
    let mut v_r_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_14940__boxed_2998_ = (crate::leanh::lean_unbox(v___y_2995_) as u8);
    v_suppressElabErrors_boxed_2999_ = (crate::leanh::lean_unbox(v_suppressElabErrors_2996_) as u8);
    v_res_3000_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0(v___y_14940__boxed_2998_, v_suppressElabErrors_boxed_2999_, v_x_2997_);
    crate::leanh::lean_dec(v_x_2997_);
    v_r_3001_ = crate::leanh::lean_box((v_res_3000_) as usize);
    return v_r_3001_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(
    mut v_ref_3003_: *mut crate::leanh::LeanObject,
    mut v_msgData_3004_: *mut crate::leanh::LeanObject,
    mut v_severity_3005_: u8,
    mut v_isSilent_3006_: u8,
    mut v___y_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: u8 = 0;
    let mut v___y_3018_: u8 = 0;
    let mut v___y_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3036_: u8 = 0;
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut v___y_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3053_: u8 = 0;
    let mut v___y_3054_: u8 = 0;
    let mut v___y_3055_: u8 = 0;
    let mut v___y_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v___y_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3078_: u8 = 0;
    let mut v___y_3079_: u8 = 0;
    let mut v___y_3080_: u8 = 0;
    let mut v___y_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3088_: u8 = 0;
    let mut v___y_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3090_: u8 = 0;
    let mut v___y_3091_: u8 = 0;
    let mut v_ref_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    let mut v___y_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: u8 = 0;
    let mut v___y_3103_: u8 = 0;
    let mut v___y_3104_: u8 = 0;
    let mut v___y_3106_: u8 = 0;
    let mut v_fileName_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3111_: u8 = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: u8 = 0;
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: u8 = 0;
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: u8 = 0;
    let mut v___x_3122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3096_ = 2;
                v___x_3121_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3005_, v___x_3096_);
                if v___x_3121_ == 0 {
                    v___y_3106_ = v___x_3121_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_3004_);
                    v___x_3122_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3004_);
                    v___y_3106_ = v___x_3122_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3022_ = lean_st_ref_take(v___y_3021_);
                v_currNamespace_3023_ = crate::leanh::lean_ctor_get(v___y_3020_, 6);
                v_openDecls_3024_ = crate::leanh::lean_ctor_get(v___y_3020_, 7);
                v_env_3025_ = crate::leanh::lean_ctor_get(v___x_3022_, 0);
                v_nextMacroScope_3026_ = crate::leanh::lean_ctor_get(v___x_3022_, 1);
                v_ngen_3027_ = crate::leanh::lean_ctor_get(v___x_3022_, 2);
                v_auxDeclNGen_3028_ = crate::leanh::lean_ctor_get(v___x_3022_, 3);
                v_traceState_3029_ = crate::leanh::lean_ctor_get(v___x_3022_, 4);
                v_cache_3030_ = crate::leanh::lean_ctor_get(v___x_3022_, 5);
                v_messages_3031_ = crate::leanh::lean_ctor_get(v___x_3022_, 6);
                v_infoState_3032_ = crate::leanh::lean_ctor_get(v___x_3022_, 7);
                v_snapshotTasks_3033_ = crate::leanh::lean_ctor_get(v___x_3022_, 8);
                v_isSharedCheck_3047_ = (!crate::leanh::lean_is_exclusive(v___x_3022_)) as u8;
                if v_isSharedCheck_3047_ == 0 {
                    v___x_3035_ = v___x_3022_;
                    v_isShared_3036_ = v_isSharedCheck_3047_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3033_);
                    crate::leanh::lean_inc(v_infoState_3032_);
                    crate::leanh::lean_inc(v_messages_3031_);
                    crate::leanh::lean_inc(v_cache_3030_);
                    crate::leanh::lean_inc(v_traceState_3029_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3028_);
                    crate::leanh::lean_inc(v_ngen_3027_);
                    crate::leanh::lean_inc(v_nextMacroScope_3026_);
                    crate::leanh::lean_inc(v_env_3025_);
                    crate::leanh::lean_dec(v___x_3022_);
                    v___x_3035_ = crate::leanh::lean_box(0);
                    v_isShared_3036_ = v_isSharedCheck_3047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_3024_);
                crate::leanh::lean_inc(v_currNamespace_3023_);
                v___x_3037_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3037_, 0, v_currNamespace_3023_);
                crate::leanh::lean_ctor_set(v___x_3037_, 1, v_openDecls_3024_);
                v___x_3038_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3038_, 0, v___x_3037_);
                crate::leanh::lean_ctor_set(v___x_3038_, 1, v___y_3014_);
                crate::leanh::lean_inc_ref(v___y_3013_);
                crate::leanh::lean_inc_ref(v___y_3016_);
                v___x_3039_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_3039_, 0, v___y_3016_);
                crate::leanh::lean_ctor_set(v___x_3039_, 1, v___y_3015_);
                crate::leanh::lean_ctor_set(v___x_3039_, 2, v___y_3019_);
                crate::leanh::lean_ctor_set(v___x_3039_, 3, v___y_3013_);
                crate::leanh::lean_ctor_set(v___x_3039_, 4, v___x_3038_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3039_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_3017_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3039_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_3018_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3039_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3006_,
                );
                v___x_3040_ = l_Lean_MessageLog_add(v___x_3039_, v_messages_3031_);
                if v_isShared_3036_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3035_, 6, v___x_3040_);
                    v___x_3042_ = v___x_3035_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_env_3025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_nextMacroScope_3026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_ngen_3027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 3, v_auxDeclNGen_3028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 4, v_traceState_3029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 5, v_cache_3030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 6, v___x_3040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 7, v_infoState_3032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 8, v_snapshotTasks_3033_);
                    v___x_3042_ = v_reuseFailAlloc_3046_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3043_ = lean_st_ref_set(v___y_3021_, v___x_3042_);
                v___x_3044_ = crate::leanh::lean_box(0);
                v___x_3045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3045_, 0, v___x_3044_);
                return v___x_3045_;
            }
            4 => {
                v___x_3057_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3004_,
                    );
                v___x_3058_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v___x_3057_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
                v_a_3059_ = crate::leanh::lean_ctor_get(v___x_3058_, 0);
                v_isSharedCheck_3072_ = (!crate::leanh::lean_is_exclusive(v___x_3058_)) as u8;
                if v_isSharedCheck_3072_ == 0 {
                    v___x_3061_ = v___x_3058_;
                    v_isShared_3062_ = v_isSharedCheck_3072_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3059_);
                    crate::leanh::lean_dec(v___x_3058_);
                    v___x_3061_ = crate::leanh::lean_box(0);
                    v_isShared_3062_ = v_isSharedCheck_3072_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_3051_, 2);
                v___x_3063_ = l_Lean_FileMap_toPosition(v___y_3051_, v___y_3050_);
                crate::leanh::lean_dec(v___y_3050_);
                v___x_3064_ = l_Lean_FileMap_toPosition(v___y_3051_, v___y_3056_);
                crate::leanh::lean_dec(v___y_3056_);
                v___x_3065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3065_, 0, v___x_3064_);
                v___x_3066_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0;
                if v___y_3055_ == 0 {
                    crate::leanh::lean_del_object(v___x_3061_);
                    crate::leanh::lean_dec_ref(v___y_3049_);
                    v___y_3013_ = v___x_3066_;
                    v___y_3014_ = v_a_3059_;
                    v___y_3015_ = v___x_3063_;
                    v___y_3016_ = v___y_3052_;
                    v___y_3017_ = v___y_3053_;
                    v___y_3018_ = v___y_3054_;
                    v___y_3019_ = v___x_3065_;
                    v___y_3020_ = v___y_3009_;
                    v___y_3021_ = v___y_3010_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3059_);
                    v___x_3067_ = l_Lean_MessageData_hasTag(v___y_3049_, v_a_3059_);
                    if v___x_3067_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3065_, 1);
                        crate::leanh::lean_dec_ref(v___x_3063_);
                        crate::leanh::lean_dec(v_a_3059_);
                        v___x_3068_ = crate::leanh::lean_box(0);
                        if v_isShared_3062_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3061_, 0, v___x_3068_);
                            v___x_3070_ = v___x_3061_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3071_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
                            v___x_3070_ = v_reuseFailAlloc_3071_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3061_);
                        v___y_3013_ = v___x_3066_;
                        v___y_3014_ = v_a_3059_;
                        v___y_3015_ = v___x_3063_;
                        v___y_3016_ = v___y_3052_;
                        v___y_3017_ = v___y_3053_;
                        v___y_3018_ = v___y_3054_;
                        v___y_3019_ = v___x_3065_;
                        v___y_3020_ = v___y_3009_;
                        v___y_3021_ = v___y_3010_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3070_;
            }
            7 => {
                v___x_3082_ = l_Lean_Syntax_getTailPos_x3f(v___y_3075_, v___y_3078_);
                crate::leanh::lean_dec(v___y_3075_);
                if crate::leanh::lean_obj_tag(v___x_3082_) == 0 {
                    crate::leanh::lean_inc(v___y_3081_);
                    v___y_3049_ = v___y_3074_;
                    v___y_3050_ = v___y_3081_;
                    v___y_3051_ = v___y_3076_;
                    v___y_3052_ = v___y_3077_;
                    v___y_3053_ = v___y_3078_;
                    v___y_3054_ = v___y_3079_;
                    v___y_3055_ = v___y_3080_;
                    v___y_3056_ = v___y_3081_;
                    state = 4;
                    continue;
                } else {
                    v_val_3083_ = crate::leanh::lean_ctor_get(v___x_3082_, 0);
                    crate::leanh::lean_inc(v_val_3083_);
                    crate::leanh::lean_dec_ref_known(v___x_3082_, 1);
                    v___y_3049_ = v___y_3074_;
                    v___y_3050_ = v___y_3081_;
                    v___y_3051_ = v___y_3076_;
                    v___y_3052_ = v___y_3077_;
                    v___y_3053_ = v___y_3078_;
                    v___y_3054_ = v___y_3079_;
                    v___y_3055_ = v___y_3080_;
                    v___y_3056_ = v_val_3083_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_3092_ = l_Lean_replaceRef(v_ref_3003_, v___y_3089_);
                v___x_3093_ = l_Lean_Syntax_getPos_x3f(v_ref_3092_, v___y_3088_);
                if crate::leanh::lean_obj_tag(v___x_3093_) == 0 {
                    v___x_3094_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3074_ = v___y_3085_;
                    v___y_3075_ = v_ref_3092_;
                    v___y_3076_ = v___y_3086_;
                    v___y_3077_ = v___y_3087_;
                    v___y_3078_ = v___y_3088_;
                    v___y_3079_ = v___y_3091_;
                    v___y_3080_ = v___y_3090_;
                    v___y_3081_ = v___x_3094_;
                    state = 7;
                    continue;
                } else {
                    v_val_3095_ = crate::leanh::lean_ctor_get(v___x_3093_, 0);
                    crate::leanh::lean_inc(v_val_3095_);
                    crate::leanh::lean_dec_ref_known(v___x_3093_, 1);
                    v___y_3074_ = v___y_3085_;
                    v___y_3075_ = v_ref_3092_;
                    v___y_3076_ = v___y_3086_;
                    v___y_3077_ = v___y_3087_;
                    v___y_3078_ = v___y_3088_;
                    v___y_3079_ = v___y_3091_;
                    v___y_3080_ = v___y_3090_;
                    v___y_3081_ = v_val_3095_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3104_ == 0 {
                    v___y_3085_ = v___y_3098_;
                    v___y_3086_ = v___y_3099_;
                    v___y_3087_ = v___y_3100_;
                    v___y_3088_ = v___y_3103_;
                    v___y_3089_ = v___y_3101_;
                    v___y_3090_ = v___y_3102_;
                    v___y_3091_ = v_severity_3005_;
                    state = 8;
                    continue;
                } else {
                    v___y_3085_ = v___y_3098_;
                    v___y_3086_ = v___y_3099_;
                    v___y_3087_ = v___y_3100_;
                    v___y_3088_ = v___y_3103_;
                    v___y_3089_ = v___y_3101_;
                    v___y_3090_ = v___y_3102_;
                    v___y_3091_ = v___x_3096_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3106_ == 0 {
                    v_fileName_3107_ = crate::leanh::lean_ctor_get(v___y_3009_, 0);
                    v_fileMap_3108_ = crate::leanh::lean_ctor_get(v___y_3009_, 1);
                    v_options_3109_ = crate::leanh::lean_ctor_get(v___y_3009_, 2);
                    v_ref_3110_ = crate::leanh::lean_ctor_get(v___y_3009_, 5);
                    v_suppressElabErrors_3111_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3009_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3112_ = crate::leanh::lean_box((v___y_3106_) as usize);
                    v___x_3113_ = crate::leanh::lean_box((v_suppressElabErrors_3111_) as usize);
                    v___f_3114_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_3114_, 0, v___x_3112_);
                    crate::leanh::lean_closure_set(v___f_3114_, 1, v___x_3113_);
                    v___x_3115_ = 1;
                    v___x_3116_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3005_, v___x_3115_);
                    if v___x_3116_ == 0 {
                        v___y_3098_ = v___f_3114_;
                        v___y_3099_ = v_fileMap_3108_;
                        v___y_3100_ = v_fileName_3107_;
                        v___y_3101_ = v_ref_3110_;
                        v___y_3102_ = v_suppressElabErrors_3111_;
                        v___y_3103_ = v___y_3106_;
                        v___y_3104_ = v___x_3116_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3117_ = l_Lean_warningAsError;
                        v___x_3118_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_3109_, v___x_3117_);
                        v___y_3098_ = v___f_3114_;
                        v___y_3099_ = v_fileMap_3108_;
                        v___y_3100_ = v_fileName_3107_;
                        v___y_3101_ = v_ref_3110_;
                        v___y_3102_ = v_suppressElabErrors_3111_;
                        v___y_3103_ = v___y_3106_;
                        v___y_3104_ = v___x_3118_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_3004_);
                    v___x_3119_ = crate::leanh::lean_box(0);
                    v___x_3120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3120_, 0, v___x_3119_);
                    return v___x_3120_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___boxed(
    mut v_ref_3123_: *mut crate::leanh::LeanObject,
    mut v_msgData_3124_: *mut crate::leanh::LeanObject,
    mut v_severity_3125_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3126_: *mut crate::leanh::LeanObject,
    mut v___y_3127_: *mut crate::leanh::LeanObject,
    mut v___y_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
    mut v___y_3131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3132_: u8 = 0;
    let mut v_isSilent_boxed_3133_: u8 = 0;
    let mut v_res_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3132_ = (crate::leanh::lean_unbox(v_severity_3125_) as u8);
    v_isSilent_boxed_3133_ = (crate::leanh::lean_unbox(v_isSilent_3126_) as u8);
    v_res_3134_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_3123_, v_msgData_3124_, v_severity_boxed_3132_, v_isSilent_boxed_3133_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
    crate::leanh::lean_dec(v___y_3130_);
    crate::leanh::lean_dec_ref(v___y_3129_);
    crate::leanh::lean_dec(v___y_3128_);
    crate::leanh::lean_dec_ref(v___y_3127_);
    crate::leanh::lean_dec(v_ref_3123_);
    return v_res_3134_;
}
pub unsafe fn l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(
    mut v_msgData_3135_: *mut crate::leanh::LeanObject,
    mut v_severity_3136_: u8,
    mut v_isSilent_3137_: u8,
    mut v___y_3138_: *mut crate::leanh::LeanObject,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
    mut v___y_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3147_ = crate::leanh::lean_ctor_get(v___y_3144_, 5);
    v___x_3148_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_3147_, v_msgData_3135_, v_severity_3136_, v_isSilent_3137_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
    return v___x_3148_;
}
pub unsafe fn l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1___boxed(
    mut v_msgData_3149_: *mut crate::leanh::LeanObject,
    mut v_severity_3150_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
    mut v___y_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3161_: u8 = 0;
    let mut v_isSilent_boxed_3162_: u8 = 0;
    let mut v_res_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3161_ = (crate::leanh::lean_unbox(v_severity_3150_) as u8);
    v_isSilent_boxed_3162_ = (crate::leanh::lean_unbox(v_isSilent_3151_) as u8);
    v_res_3163_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v_msgData_3149_, v_severity_boxed_3161_, v_isSilent_boxed_3162_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
    crate::leanh::lean_dec(v___y_3159_);
    crate::leanh::lean_dec_ref(v___y_3158_);
    crate::leanh::lean_dec(v___y_3157_);
    crate::leanh::lean_dec_ref(v___y_3156_);
    crate::leanh::lean_dec(v___y_3155_);
    crate::leanh::lean_dec_ref(v___y_3154_);
    crate::leanh::lean_dec(v___y_3153_);
    crate::leanh::lean_dec_ref(v___y_3152_);
    return v_res_3163_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3167_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__1;
    v___x_3168_ = l_Lean_MessageData_ofFormat(v___x_3167_);
    return v___x_3168_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3169_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3170_ = lean_mk_empty_array_with_capacity(v___x_3169_);
    v___x_3171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3171_, 0, v___x_3170_);
    return v___x_3171_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3173_ = l_Lean_Elab_Tactic_instInhabitedTacticFinishedSnapshot;
    v___x_3174_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3173_);
    return v___x_3174_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3179_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__8;
    v___x_3180_ = l_Lean_MessageData_ofFormat(v___x_3179_);
    return v___x_3180_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3184_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
    v___x_3185_ = crate::leanh::lean_unsigned_to_nat(39);
    v___x_3186_ = crate::leanh::lean_unsigned_to_nat(52);
    v___x_3187_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11;
    v___x_3188_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10;
    v___x_3189_ = l_mkPanicMessageWithDecl(
        v___x_3188_,
        v___x_3187_,
        v___x_3186_,
        v___x_3185_,
        v___x_3184_,
    );
    return v___x_3189_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
    v___x_3191_ = crate::leanh::lean_unsigned_to_nat(37);
    v___x_3192_ = crate::leanh::lean_unsigned_to_nat(44);
    v___x_3193_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__11;
    v___x_3194_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10;
    v___x_3195_ = l_mkPanicMessageWithDecl(
        v___x_3194_,
        v___x_3193_,
        v___x_3192_,
        v___x_3191_,
        v___x_3190_,
    );
    return v___x_3195_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(
    mut v___x_3196_: *mut crate::leanh::LeanObject,
    mut v___x_3197_: *mut crate::leanh::LeanObject,
    mut v___x_3198_: *mut crate::leanh::LeanObject,
    mut v___x_3199_: *mut crate::leanh::LeanObject,
    mut v___x_3200_: *mut crate::leanh::LeanObject,
    mut v___x_3201_: u8,
    mut v_val_3202_: *mut crate::leanh::LeanObject,
    mut v_x_3203_: *mut crate::leanh::LeanObject,
    mut v___y_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
    mut v___y_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
    mut v___y_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
    mut v___y_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tacSnap_x3f_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: usize = 0;
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u64 = 0;
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3246_: u8 = 0;
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3253_: u8 = 0;
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: u8 = 0;
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3261_: u8 = 0;
    let mut v_unused_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3266_: u8 = 0;
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3276_: u8 = 0;
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut v_unused_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3213_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
                v___x_3214_ = 2;
                v___x_3215_ = 0;
                v___x_3216_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_3213_, v___x_3214_, v___x_3215_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
                if crate::leanh::lean_obj_tag(v___x_3216_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3216_, 1);
                    v_tacSnap_x3f_3217_ = crate::leanh::lean_ctor_get(v___y_3206_, 6);
                    if crate::leanh::lean_obj_tag(v_tacSnap_x3f_3217_) == 1 {
                        v_val_3218_ = crate::leanh::lean_ctor_get(v_tacSnap_x3f_3217_, 0);
                        v___x_3219_ = l_Lean_Core_getMessageLog___redArg(v___y_3211_);
                        if crate::leanh::lean_obj_tag(v___x_3219_) == 0 {
                            v_a_3220_ = crate::leanh::lean_ctor_get(v___x_3219_, 0);
                            crate::leanh::lean_inc(v_a_3220_);
                            crate::leanh::lean_dec_ref_known(v___x_3219_, 1);
                            v___x_3221_ =
                                l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_a_3220_);
                            v___x_3222_ = crate::leanh::lean_unsigned_to_nat(32);
                            v___x_3223_ = lean_mk_empty_array_with_capacity(v___x_3222_);
                            v___x_3224_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3);
                            v___x_3225_ = 5usize;
                            crate::leanh::lean_inc_n(v___x_3196_, 2);
                            v___x_3226_ = crate::leanh::lean_alloc_ctor(
                                0,
                                4,
                                (core::mem::size_of::<usize>() * 1) as u32,
                            );
                            crate::leanh::lean_ctor_set(v___x_3226_, 0, v___x_3224_);
                            crate::leanh::lean_ctor_set(v___x_3226_, 1, v___x_3223_);
                            crate::leanh::lean_ctor_set(v___x_3226_, 2, v___x_3196_);
                            crate::leanh::lean_ctor_set(v___x_3226_, 3, v___x_3196_);
                            crate::leanh::lean_ctor_set_usize(v___x_3226_, 4, v___x_3225_);
                            v_new_3227_ = crate::leanh::lean_ctor_get(v_val_3218_, 1);
                            v___x_3228_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__4;
                            v___x_3229_ = l_Lean_Name_mkStr5(
                                v___x_3197_,
                                v___x_3198_,
                                v___x_3199_,
                                v___x_3200_,
                                v___x_3228_,
                            );
                            v___x_3230_ = l_Lean_Name_toString(v___x_3229_, v___x_3201_);
                            v___x_3231_ = crate::leanh::lean_box(0);
                            v___x_3232_ = 0u64;
                            v___x_3233_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                            crate::leanh::lean_ctor_set(v___x_3233_, 0, v___x_3226_);
                            crate::leanh::lean_ctor_set_uint64(
                                v___x_3233_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_3232_,
                            );
                            v___x_3234_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_3234_, 0, v___x_3230_);
                            crate::leanh::lean_ctor_set(v___x_3234_, 1, v___x_3221_);
                            crate::leanh::lean_ctor_set(v___x_3234_, 2, v___x_3231_);
                            crate::leanh::lean_ctor_set(v___x_3234_, 3, v___x_3233_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_3234_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                                v___x_3215_,
                            );
                            v___x_3235_ = crate::leanh::lean_box(0);
                            v___x_3236_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5);
                            v___x_3237_ = lean_mk_empty_array_with_capacity(v___x_3196_);
                            crate::leanh::lean_dec(v___x_3196_);
                            v___x_3238_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3238_, 0, v___x_3234_);
                            crate::leanh::lean_ctor_set(v___x_3238_, 1, v___x_3235_);
                            crate::leanh::lean_ctor_set(v___x_3238_, 2, v___x_3231_);
                            crate::leanh::lean_ctor_set(v___x_3238_, 3, v___x_3236_);
                            crate::leanh::lean_ctor_set(v___x_3238_, 4, v___x_3237_);
                            v___x_3239_ = lean_io_promise_resolve(v___x_3238_, v_new_3227_);
                            v_cancelTk_x3f_3240_ = crate::leanh::lean_ctor_get(v___y_3210_, 12);
                            if crate::leanh::lean_obj_tag(v_cancelTk_x3f_3240_) == 1 {
                                v_ref_3241_ = crate::leanh::lean_ctor_get(v___y_3210_, 5);
                                v_val_3242_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_3240_, 0);
                                v___x_3243_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_3242_);
                                if crate::leanh::lean_obj_tag(v___x_3243_) == 0 {
                                    v_isSharedCheck_3277_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3243_)) as u8;
                                    if v_isSharedCheck_3277_ == 0 {
                                        v_unused_3278_ =
                                            crate::leanh::lean_ctor_get(v___x_3243_, 0);
                                        crate::leanh::lean_dec(v_unused_3278_);
                                        v___x_3245_ = v___x_3243_;
                                        v_isShared_3246_ = v_isSharedCheck_3277_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_3243_);
                                        v___x_3245_ = crate::leanh::lean_box(0);
                                        v_isShared_3246_ = v_isSharedCheck_3277_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    return v___x_3243_;
                                }
                            } else {
                                v___x_3279_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__13);
                                v___x_3280_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_3279_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
                                return v___x_3280_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3200_);
                            crate::leanh::lean_dec_ref(v___x_3199_);
                            crate::leanh::lean_dec_ref(v___x_3198_);
                            crate::leanh::lean_dec_ref(v___x_3197_);
                            crate::leanh::lean_dec(v___x_3196_);
                            v_a_3281_ = crate::leanh::lean_ctor_get(v___x_3219_, 0);
                            v_isSharedCheck_3288_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3219_)) as u8;
                            if v_isSharedCheck_3288_ == 0 {
                                v___x_3283_ = v___x_3219_;
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3281_);
                                crate::leanh::lean_dec(v___x_3219_);
                                v___x_3283_ = crate::leanh::lean_box(0);
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3200_);
                        crate::leanh::lean_dec_ref(v___x_3199_);
                        crate::leanh::lean_dec_ref(v___x_3198_);
                        crate::leanh::lean_dec_ref(v___x_3197_);
                        crate::leanh::lean_dec(v___x_3196_);
                        v___x_3289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__14);
                        v___x_3290_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_3289_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
                        return v___x_3290_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3200_);
                    crate::leanh::lean_dec_ref(v___x_3199_);
                    crate::leanh::lean_dec_ref(v___x_3198_);
                    crate::leanh::lean_dec_ref(v___x_3197_);
                    crate::leanh::lean_dec(v___x_3196_);
                    return v___x_3216_;
                }
            }
            1 => {
                v___x_3247_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6;
                v___x_3248_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_3247_);
                if crate::leanh::lean_obj_tag(v___x_3248_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3248_, 1);
                    crate::leanh::lean_del_object(v___x_3245_);
                    v___x_3249_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
                    v___x_3250_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_3249_, v___x_3214_, v___x_3215_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
                    if crate::leanh::lean_obj_tag(v___x_3250_) == 0 {
                        v_isSharedCheck_3261_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3250_)) as u8;
                        if v_isSharedCheck_3261_ == 0 {
                            v_unused_3262_ = crate::leanh::lean_ctor_get(v___x_3250_, 0);
                            crate::leanh::lean_dec(v_unused_3262_);
                            v___x_3252_ = v___x_3250_;
                            v_isShared_3253_ = v_isSharedCheck_3261_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3250_);
                            v___x_3252_ = crate::leanh::lean_box(0);
                            v_isShared_3253_ = v_isSharedCheck_3261_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_3250_;
                    }
                } else {
                    v_a_3263_ = crate::leanh::lean_ctor_get(v___x_3248_, 0);
                    v_isSharedCheck_3276_ = (!crate::leanh::lean_is_exclusive(v___x_3248_)) as u8;
                    if v_isSharedCheck_3276_ == 0 {
                        v___x_3265_ = v___x_3248_;
                        v_isShared_3266_ = v_isSharedCheck_3276_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3263_);
                        crate::leanh::lean_dec(v___x_3248_);
                        v___x_3265_ = crate::leanh::lean_box(0);
                        v_isShared_3266_ = v_isSharedCheck_3276_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3254_ = crate::leanh::lean_box(0);
                v___x_3255_ = lean_io_promise_resolve(v___x_3254_, v_val_3202_);
                v___x_3256_ = l_IO_CancelToken_isSet(v_val_3242_);
                if v___x_3256_ == 0 {
                    if v_isShared_3253_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3252_, 0, v___x_3254_);
                        v___x_3258_ = v___x_3252_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3259_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3254_);
                        v___x_3258_ = v_reuseFailAlloc_3259_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3252_);
                    v___x_3260_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
                    return v___x_3260_;
                }
            }
            3 => {
                return v___x_3258_;
            }
            4 => {
                v___x_3267_ = lean_io_error_to_string(v_a_3263_);
                if v_isShared_3246_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3245_, 3);
                    crate::leanh::lean_ctor_set(v___x_3245_, 0, v___x_3267_);
                    v___x_3269_ = v___x_3245_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3275_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3267_);
                    v___x_3269_ = v_reuseFailAlloc_3275_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3270_ = l_Lean_MessageData_ofFormat(v___x_3269_);
                crate::leanh::lean_inc(v_ref_3241_);
                v___x_3271_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3271_, 0, v_ref_3241_);
                crate::leanh::lean_ctor_set(v___x_3271_, 1, v___x_3270_);
                if v_isShared_3266_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3265_, 0, v___x_3271_);
                    v___x_3273_ = v___x_3265_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
                    v___x_3273_ = v_reuseFailAlloc_3274_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3273_;
            }
            7 => {
                if v_isShared_3284_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
                    v___x_3286_ = v_reuseFailAlloc_3287_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3291_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_3292_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_3293_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3294_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3295_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_3296_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_val_3297_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_x_3298_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_3299_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_3300_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3301_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3302_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3303_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3304_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3305_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3306_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3307_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_15320__boxed_3308_: u8 = 0;
    let mut v_res_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15320__boxed_3308_ = (crate::leanh::lean_unbox(v___x_3296_) as u8);
    v_res_3309_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0(v___x_3291_, v___x_3292_, v___x_3293_, v___x_3294_, v___x_3295_, v___x_15320__boxed_3308_, v_val_3297_, v_x_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
    crate::leanh::lean_dec(v___y_3306_);
    crate::leanh::lean_dec_ref(v___y_3305_);
    crate::leanh::lean_dec(v___y_3304_);
    crate::leanh::lean_dec_ref(v___y_3303_);
    crate::leanh::lean_dec(v___y_3302_);
    crate::leanh::lean_dec_ref(v___y_3301_);
    crate::leanh::lean_dec(v___y_3300_);
    crate::leanh::lean_dec_ref(v___y_3299_);
    crate::leanh::lean_dec(v_val_3297_);
    return v_res_3309_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(
    mut v_x_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
    mut v_a_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
    mut v_a_3319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3341_: u8 = 0;
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3347_: u8 = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9892__overap_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3321_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0;
                v___x_3322_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1;
                v___x_3323_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2;
                v___x_3324_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3;
                v___x_3325_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__5;
                v___x_3326_ = l_Lean_Syntax_isOfKind(v_x_3311_, v___x_3325_);
                if v___x_3326_ == 0 {
                    v___x_3327_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
                    return v___x_3327_;
                } else {
                    v___x_3328_ = lean_io_promise_new();
                    v___x_3329_ = l_Lean_Server_Test_Cancel_onceRef;
                    v___x_3330_ = lean_st_ref_take(v___x_3329_);
                    v___x_3331_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3332_ = crate::leanh::lean_box((v___x_3326_) as usize);
                    crate::leanh::lean_inc(v___x_3328_);
                    v___f_3333_ = crate::leanh::lean_alloc_closure(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___boxed as *mut core::ffi::c_void, 17, 7);
                    crate::leanh::lean_closure_set(v___f_3333_, 0, v___x_3331_);
                    crate::leanh::lean_closure_set(v___f_3333_, 1, v___x_3321_);
                    crate::leanh::lean_closure_set(v___f_3333_, 2, v___x_3322_);
                    crate::leanh::lean_closure_set(v___f_3333_, 3, v___x_3323_);
                    crate::leanh::lean_closure_set(v___f_3333_, 4, v___x_3324_);
                    crate::leanh::lean_closure_set(v___f_3333_, 5, v___x_3332_);
                    crate::leanh::lean_closure_set(v___f_3333_, 6, v___x_3328_);
                    if crate::leanh::lean_obj_tag(v___x_3330_) == 0 {
                        v___x_3351_ = l_IO_Promise_result_x21___redArg(v___x_3328_);
                        crate::leanh::lean_dec(v___x_3328_);
                        v___y_3335_ = v___x_3351_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3328_);
                        v_val_3352_ = crate::leanh::lean_ctor_get(v___x_3330_, 0);
                        crate::leanh::lean_inc(v_val_3352_);
                        v___y_3335_ = v_val_3352_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3336_, 0, v___y_3335_);
                v___x_3337_ = lean_st_ref_set(v___x_3329_, v___x_3336_);
                if crate::leanh::lean_obj_tag(v___x_3330_) == 1 {
                    crate::leanh::lean_dec_ref(v___f_3333_);
                    v_val_3338_ = crate::leanh::lean_ctor_get(v___x_3330_, 0);
                    v_isSharedCheck_3347_ = (!crate::leanh::lean_is_exclusive(v___x_3330_)) as u8;
                    if v_isSharedCheck_3347_ == 0 {
                        v___x_3340_ = v___x_3330_;
                        v_isShared_3341_ = v_isSharedCheck_3347_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3338_);
                        crate::leanh::lean_dec(v___x_3330_);
                        v___x_3340_ = crate::leanh::lean_box(0);
                        v_isShared_3341_ = v_isSharedCheck_3347_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3330_);
                    v___x_3348_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0;
                    v___x_9892__overap_3349_ = lean_dbg_trace(v___x_3348_, v___f_3333_);
                    crate::leanh::lean_inc(v_a_3319_);
                    crate::leanh::lean_inc_ref(v_a_3318_);
                    crate::leanh::lean_inc(v_a_3317_);
                    crate::leanh::lean_inc_ref(v_a_3316_);
                    crate::leanh::lean_inc(v_a_3315_);
                    crate::leanh::lean_inc_ref(v_a_3314_);
                    crate::leanh::lean_inc(v_a_3313_);
                    crate::leanh::lean_inc_ref(v_a_3312_);
                    v___x_3350_ = crate::leanh::lean_apply_9(
                        v___x_9892__overap_3349_,
                        v_a_3312_,
                        v_a_3313_,
                        v_a_3314_,
                        v_a_3315_,
                        v_a_3316_,
                        v_a_3317_,
                        v_a_3318_,
                        v_a_3319_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3350_;
                }
            }
            2 => {
                v___x_3342_ = lean_io_wait(v_val_3338_);
                crate::leanh::lean_dec(v___x_3342_);
                v___x_3343_ = crate::leanh::lean_box(0);
                if v_isShared_3341_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3340_, 0);
                    crate::leanh::lean_ctor_set(v___x_3340_, 0, v___x_3343_);
                    v___x_3345_ = v___x_3340_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
                    v___x_3345_ = v_reuseFailAlloc_3346_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___boxed(
    mut v_x_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_a_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
    mut v_a_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1(v_x_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_);
    crate::leanh::lean_dec(v_a_3361_);
    crate::leanh::lean_dec_ref(v_a_3360_);
    crate::leanh::lean_dec(v_a_3359_);
    crate::leanh::lean_dec_ref(v_a_3358_);
    crate::leanh::lean_dec(v_a_3357_);
    crate::leanh::lean_dec_ref(v_a_3356_);
    crate::leanh::lean_dec(v_a_3355_);
    crate::leanh::lean_dec_ref(v_a_3354_);
    return v_res_3363_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(
    mut v_val_3364_: *mut crate::leanh::LeanObject,
    mut v_inst_3365_: *mut crate::leanh::LeanObject,
    mut v_a_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
    mut v___y_3374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3376_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___redArg(v_val_3364_);
    return v___x_3376_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2___boxed(
    mut v_val_3377_: *mut crate::leanh::LeanObject,
    mut v_inst_3378_: *mut crate::leanh::LeanObject,
    mut v_a_3379_: *mut crate::leanh::LeanObject,
    mut v___y_3380_: *mut crate::leanh::LeanObject,
    mut v___y_3381_: *mut crate::leanh::LeanObject,
    mut v___y_3382_: *mut crate::leanh::LeanObject,
    mut v___y_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3389_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__2(v_val_3377_, v_inst_3378_, v_a_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
    crate::leanh::lean_dec(v___y_3387_);
    crate::leanh::lean_dec_ref(v___y_3386_);
    crate::leanh::lean_dec(v___y_3385_);
    crate::leanh::lean_dec_ref(v___y_3384_);
    crate::leanh::lean_dec(v___y_3383_);
    crate::leanh::lean_dec_ref(v___y_3382_);
    crate::leanh::lean_dec(v___y_3381_);
    crate::leanh::lean_dec_ref(v___y_3380_);
    crate::leanh::lean_dec_ref(v_val_3377_);
    return v_res_3389_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(
    mut v_ref_3390_: *mut crate::leanh::LeanObject,
    mut v_msgData_3391_: *mut crate::leanh::LeanObject,
    mut v_severity_3392_: u8,
    mut v_isSilent_3393_: u8,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3403_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg(v_ref_3390_, v_msgData_3391_, v_severity_3392_, v_isSilent_3393_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
    return v___x_3403_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___boxed(
    mut v_ref_3404_: *mut crate::leanh::LeanObject,
    mut v_msgData_3405_: *mut crate::leanh::LeanObject,
    mut v_severity_3406_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3407_: *mut crate::leanh::LeanObject,
    mut v___y_3408_: *mut crate::leanh::LeanObject,
    mut v___y_3409_: *mut crate::leanh::LeanObject,
    mut v___y_3410_: *mut crate::leanh::LeanObject,
    mut v___y_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
    mut v___y_3415_: *mut crate::leanh::LeanObject,
    mut v___y_3416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3417_: u8 = 0;
    let mut v_isSilent_boxed_3418_: u8 = 0;
    let mut v_res_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3417_ = (crate::leanh::lean_unbox(v_severity_3406_) as u8);
    v_isSilent_boxed_3418_ = (crate::leanh::lean_unbox(v_isSilent_3407_) as u8);
    v_res_3419_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1(v_ref_3404_, v_msgData_3405_, v_severity_boxed_3417_, v_isSilent_boxed_3418_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
    crate::leanh::lean_dec(v___y_3415_);
    crate::leanh::lean_dec_ref(v___y_3414_);
    crate::leanh::lean_dec(v___y_3413_);
    crate::leanh::lean_dec_ref(v___y_3412_);
    crate::leanh::lean_dec(v___y_3411_);
    crate::leanh::lean_dec_ref(v___y_3410_);
    crate::leanh::lean_dec(v___y_3409_);
    crate::leanh::lean_dec_ref(v___y_3408_);
    crate::leanh::lean_dec(v_ref_3404_);
    return v_res_3419_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ = crate::leanh::lean_box(0);
    v___x_3422_ = lean_st_mk_ref(v___x_3421_);
    v___x_3423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3423_, 0, v___x_3422_);
    return v___x_3423_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2____boxed(
    mut v_a_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_();
    return v_res_3425_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3427_ = l_IO_CancelToken_new();
                v___x_3428_ = l_Lean_Server_Test_Cancel_unblockedCancelTkRef;
                v___x_3429_ = lean_st_ref_take(v___x_3428_);
                if crate::leanh::lean_obj_tag(v___x_3429_) == 0 {
                    crate::leanh::lean_inc_ref(v___x_3427_);
                    v___x_3434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3434_, 0, v___x_3427_);
                    v_fst_3431_ = v___x_3427_;
                    v_snd_3432_ = v___x_3434_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_3427_);
                    v_val_3435_ = crate::leanh::lean_ctor_get(v___x_3429_, 0);
                    crate::leanh::lean_inc(v_val_3435_);
                    v_fst_3431_ = v_val_3435_;
                    v_snd_3432_ = v___x_3429_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3433_ = lean_st_ref_set(v___x_3428_, v_snd_3432_);
                return v_fst_3431_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk___boxed(
    mut v_a_3436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3437_ =
        l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
    return v_res_3437_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: u8 = 0;
    let mut v___x_3457_: u32 = 0;
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3455_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
                v___x_3456_ = l_IO_CancelToken_isSet(v___x_3455_);
                crate::leanh::lean_dec_ref(v___x_3455_);
                if v___x_3456_ == 0 {
                    v___x_3457_ = 30;
                    v___x_3458_ = l_IO_sleep(v___x_3457_);
                    state = 0;
                    continue;
                } else {
                    v___x_3460_ = crate::leanh::lean_box(0);
                    v___x_3461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3461_, 0, v___x_3460_);
                    return v___x_3461_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg___boxed(
    mut v___y_3462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3463_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
    return v_res_3463_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3466_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
    v___x_3467_ = crate::leanh::lean_unsigned_to_nat(37);
    v___x_3468_ = crate::leanh::lean_unsigned_to_nat(89);
    v___x_3469_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1;
    v___x_3470_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10;
    v___x_3471_ = l_mkPanicMessageWithDecl(
        v___x_3470_,
        v___x_3469_,
        v___x_3468_,
        v___x_3467_,
        v___x_3466_,
    );
    return v___x_3471_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(
    mut v___x_3472_: *mut crate::leanh::LeanObject,
    mut v___x_3473_: *mut crate::leanh::LeanObject,
    mut v___x_3474_: *mut crate::leanh::LeanObject,
    mut v___x_3475_: *mut crate::leanh::LeanObject,
    mut v___x_3476_: *mut crate::leanh::LeanObject,
    mut v___x_3477_: u8,
    mut v_val_3478_: *mut crate::leanh::LeanObject,
    mut v_x_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: u8 = 0;
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3495_: u8 = 0;
    let mut v_tacSnap_x3f_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: usize = 0;
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_new_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u64 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v_ref_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3546_: u8 = 0;
    let mut v_isSharedCheck_3547_: u8 = 0;
    let mut v_unused_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3552_: u8 = 0;
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3556_: u8 = 0;
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v_unused_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3489_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
                v___x_3490_ = 2;
                v___x_3491_ = 0;
                v___x_3492_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_3489_, v___x_3490_, v___x_3491_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
                if crate::leanh::lean_obj_tag(v___x_3492_) == 0 {
                    v_isSharedCheck_3559_ = (!crate::leanh::lean_is_exclusive(v___x_3492_)) as u8;
                    if v_isSharedCheck_3559_ == 0 {
                        v_unused_3560_ = crate::leanh::lean_ctor_get(v___x_3492_, 0);
                        crate::leanh::lean_dec(v_unused_3560_);
                        v___x_3494_ = v___x_3492_;
                        v_isShared_3495_ = v_isSharedCheck_3559_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3492_);
                        v___x_3494_ = crate::leanh::lean_box(0);
                        v_isShared_3495_ = v_isSharedCheck_3559_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3476_);
                    crate::leanh::lean_dec_ref(v___x_3475_);
                    crate::leanh::lean_dec_ref(v___x_3474_);
                    crate::leanh::lean_dec_ref(v___x_3473_);
                    crate::leanh::lean_dec(v___x_3472_);
                    return v___x_3492_;
                }
            }
            1 => {
                v_tacSnap_x3f_3496_ = crate::leanh::lean_ctor_get(v___y_3482_, 6);
                if crate::leanh::lean_obj_tag(v_tacSnap_x3f_3496_) == 1 {
                    v_val_3497_ = crate::leanh::lean_ctor_get(v_tacSnap_x3f_3496_, 0);
                    v___x_3498_ = l_Lean_Core_getMessageLog___redArg(v___y_3487_);
                    if crate::leanh::lean_obj_tag(v___x_3498_) == 0 {
                        v_a_3499_ = crate::leanh::lean_ctor_get(v___x_3498_, 0);
                        crate::leanh::lean_inc(v_a_3499_);
                        crate::leanh::lean_dec_ref_known(v___x_3498_, 1);
                        v___x_3500_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_a_3499_);
                        v___x_3501_ = crate::leanh::lean_unsigned_to_nat(32);
                        v___x_3502_ = lean_mk_empty_array_with_capacity(v___x_3501_);
                        v___x_3503_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__3);
                        v___x_3504_ = 5usize;
                        crate::leanh::lean_inc_n(v___x_3472_, 2);
                        v___x_3505_ = crate::leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        crate::leanh::lean_ctor_set(v___x_3505_, 0, v___x_3503_);
                        crate::leanh::lean_ctor_set(v___x_3505_, 1, v___x_3502_);
                        crate::leanh::lean_ctor_set(v___x_3505_, 2, v___x_3472_);
                        crate::leanh::lean_ctor_set(v___x_3505_, 3, v___x_3472_);
                        crate::leanh::lean_ctor_set_usize(v___x_3505_, 4, v___x_3504_);
                        v_new_3506_ = crate::leanh::lean_ctor_get(v_val_3497_, 1);
                        v___x_3507_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__0;
                        v___x_3508_ = l_Lean_Name_mkStr5(
                            v___x_3473_,
                            v___x_3474_,
                            v___x_3475_,
                            v___x_3476_,
                            v___x_3507_,
                        );
                        v___x_3509_ = l_Lean_Name_toString(v___x_3508_, v___x_3477_);
                        v___x_3510_ = crate::leanh::lean_box(0);
                        v___x_3511_ = 0u64;
                        v___x_3512_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                        crate::leanh::lean_ctor_set(v___x_3512_, 0, v___x_3505_);
                        crate::leanh::lean_ctor_set_uint64(
                            v___x_3512_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_3511_,
                        );
                        v___x_3513_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3509_);
                        crate::leanh::lean_ctor_set(v___x_3513_, 1, v___x_3500_);
                        crate::leanh::lean_ctor_set(v___x_3513_, 2, v___x_3510_);
                        crate::leanh::lean_ctor_set(v___x_3513_, 3, v___x_3512_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3513_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                            v___x_3491_,
                        );
                        v___x_3514_ = crate::leanh::lean_box(0);
                        v___x_3515_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__5);
                        v___x_3516_ = lean_mk_empty_array_with_capacity(v___x_3472_);
                        crate::leanh::lean_dec(v___x_3472_);
                        v___x_3517_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3517_, 0, v___x_3513_);
                        crate::leanh::lean_ctor_set(v___x_3517_, 1, v___x_3514_);
                        crate::leanh::lean_ctor_set(v___x_3517_, 2, v___x_3510_);
                        crate::leanh::lean_ctor_set(v___x_3517_, 3, v___x_3515_);
                        crate::leanh::lean_ctor_set(v___x_3517_, 4, v___x_3516_);
                        v___x_3518_ = lean_io_promise_resolve(v___x_3517_, v_new_3506_);
                        v___x_3519_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
                        if crate::leanh::lean_obj_tag(v___x_3519_) == 0 {
                            v_isSharedCheck_3547_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3519_)) as u8;
                            if v_isSharedCheck_3547_ == 0 {
                                v_unused_3548_ = crate::leanh::lean_ctor_get(v___x_3519_, 0);
                                crate::leanh::lean_dec(v_unused_3548_);
                                v___x_3521_ = v___x_3519_;
                                v_isShared_3522_ = v_isSharedCheck_3547_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3519_);
                                v___x_3521_ = crate::leanh::lean_box(0);
                                v_isShared_3522_ = v_isSharedCheck_3547_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3494_);
                            return v___x_3519_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3494_);
                        crate::leanh::lean_dec_ref(v___x_3476_);
                        crate::leanh::lean_dec_ref(v___x_3475_);
                        crate::leanh::lean_dec_ref(v___x_3474_);
                        crate::leanh::lean_dec_ref(v___x_3473_);
                        crate::leanh::lean_dec(v___x_3472_);
                        v_a_3549_ = crate::leanh::lean_ctor_get(v___x_3498_, 0);
                        v_isSharedCheck_3556_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3498_)) as u8;
                        if v_isSharedCheck_3556_ == 0 {
                            v___x_3551_ = v___x_3498_;
                            v_isShared_3552_ = v_isSharedCheck_3556_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3549_);
                            crate::leanh::lean_dec(v___x_3498_);
                            v___x_3551_ = crate::leanh::lean_box(0);
                            v_isShared_3552_ = v_isSharedCheck_3556_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3494_);
                    crate::leanh::lean_dec_ref(v___x_3476_);
                    crate::leanh::lean_dec_ref(v___x_3475_);
                    crate::leanh::lean_dec_ref(v___x_3474_);
                    crate::leanh::lean_dec_ref(v___x_3473_);
                    crate::leanh::lean_dec(v___x_3472_);
                    v___x_3557_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__2);
                    v___x_3558_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_3557_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
                    return v___x_3558_;
                }
            }
            2 => {
                v___x_3523_ = l_IO_CancelToken_isSet(v_val_3478_);
                if v___x_3523_ == 0 {
                    crate::leanh::lean_del_object(v___x_3494_);
                    v___x_3524_ = crate::leanh::lean_box(0);
                    if v_isShared_3522_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3521_, 0, v___x_3524_);
                        v___x_3526_ = v___x_3521_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
                        v___x_3526_ = v_reuseFailAlloc_3527_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3521_);
                    v___x_3528_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6;
                    v___x_3529_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_3528_);
                    if crate::leanh::lean_obj_tag(v___x_3529_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3529_, 1);
                        crate::leanh::lean_del_object(v___x_3494_);
                        v___x_3530_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
                        v___x_3531_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_3530_, v___x_3490_, v___x_3491_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
                        return v___x_3531_;
                    } else {
                        v_a_3532_ = crate::leanh::lean_ctor_get(v___x_3529_, 0);
                        v_isSharedCheck_3546_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3529_)) as u8;
                        if v_isSharedCheck_3546_ == 0 {
                            v___x_3534_ = v___x_3529_;
                            v_isShared_3535_ = v_isSharedCheck_3546_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3532_);
                            crate::leanh::lean_dec(v___x_3529_);
                            v___x_3534_ = crate::leanh::lean_box(0);
                            v_isShared_3535_ = v_isSharedCheck_3546_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3526_;
            }
            4 => {
                v_ref_3536_ = crate::leanh::lean_ctor_get(v___y_3486_, 5);
                v___x_3537_ = lean_io_error_to_string(v_a_3532_);
                if v_isShared_3495_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3494_, 3);
                    crate::leanh::lean_ctor_set(v___x_3494_, 0, v___x_3537_);
                    v___x_3539_ = v___x_3494_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3545_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3537_);
                    v___x_3539_ = v_reuseFailAlloc_3545_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3540_ = l_Lean_MessageData_ofFormat(v___x_3539_);
                crate::leanh::lean_inc(v_ref_3536_);
                v___x_3541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3541_, 0, v_ref_3536_);
                crate::leanh::lean_ctor_set(v___x_3541_, 1, v___x_3540_);
                if v_isShared_3535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3534_, 0, v___x_3541_);
                    v___x_3543_ = v___x_3534_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
                    v___x_3543_ = v_reuseFailAlloc_3544_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3543_;
            }
            7 => {
                if v_isShared_3552_ == 0 {
                    v___x_3554_ = v___x_3551_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3555_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
                    v___x_3554_ = v_reuseFailAlloc_3555_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3561_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_3562_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_3563_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3564_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3565_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_3566_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_val_3567_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_x_3568_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_3569_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_3570_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3571_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3572_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3573_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3574_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3575_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3576_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3577_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_7300__boxed_3578_: u8 = 0;
    let mut v_res_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7300__boxed_3578_ = (crate::leanh::lean_unbox(v___x_3566_) as u8);
    v_res_3579_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0(v___x_3561_, v___x_3562_, v___x_3563_, v___x_3564_, v___x_3565_, v___x_7300__boxed_3578_, v_val_3567_, v_x_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
    crate::leanh::lean_dec(v___y_3576_);
    crate::leanh::lean_dec_ref(v___y_3575_);
    crate::leanh::lean_dec(v___y_3574_);
    crate::leanh::lean_dec_ref(v___y_3573_);
    crate::leanh::lean_dec(v___y_3572_);
    crate::leanh::lean_dec_ref(v___y_3571_);
    crate::leanh::lean_dec(v___y_3570_);
    crate::leanh::lean_dec_ref(v___y_3569_);
    crate::leanh::lean_dec_ref(v_val_3567_);
    return v_res_3579_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3580_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
    v___x_3581_ = crate::leanh::lean_unsigned_to_nat(39);
    v___x_3582_ = crate::leanh::lean_unsigned_to_nat(84);
    v___x_3583_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___closed__1;
    v___x_3584_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10;
    v___x_3585_ = l_mkPanicMessageWithDecl(
        v___x_3584_,
        v___x_3583_,
        v___x_3582_,
        v___x_3581_,
        v___x_3580_,
    );
    return v___x_3585_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(
    mut v_x_3586_: *mut crate::leanh::LeanObject,
    mut v_a_3587_: *mut crate::leanh::LeanObject,
    mut v_a_3588_: *mut crate::leanh::LeanObject,
    mut v_a_3589_: *mut crate::leanh::LeanObject,
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
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    v___x_3596_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0;
    v___x_3597_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1;
    v___x_3598_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2;
    v___x_3599_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3;
    v___x_3600_ = l_Lean_Server_Test_Cancel_tacticWait__for__unblock___closed__1;
    v___x_3601_ = l_Lean_Syntax_isOfKind(v_x_3586_, v___x_3600_);
    if v___x_3601_ == 0 {
        let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3602_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
        return v___x_3602_;
    } else {
        let mut v_cancelTk_x3f_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_cancelTk_x3f_3603_ = crate::leanh::lean_ctor_get(v_a_3593_, 12);
        if crate::leanh::lean_obj_tag(v_cancelTk_x3f_3603_) == 1 {
            let mut v_val_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6757__overap_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_3604_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_3603_, 0);
            v___x_3605_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_3606_ = crate::leanh::lean_box((v___x_3601_) as usize);
            crate::leanh::lean_inc(v_val_3604_);
            v___f_3607_ = crate::leanh::lean_alloc_closure(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___lam__0___boxed as *mut core::ffi::c_void, 17, 7);
            crate::leanh::lean_closure_set(v___f_3607_, 0, v___x_3605_);
            crate::leanh::lean_closure_set(v___f_3607_, 1, v___x_3596_);
            crate::leanh::lean_closure_set(v___f_3607_, 2, v___x_3597_);
            crate::leanh::lean_closure_set(v___f_3607_, 3, v___x_3598_);
            crate::leanh::lean_closure_set(v___f_3607_, 4, v___x_3599_);
            crate::leanh::lean_closure_set(v___f_3607_, 5, v___x_3606_);
            crate::leanh::lean_closure_set(v___f_3607_, 6, v_val_3604_);
            v___x_3608_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0;
            v___x_6757__overap_3609_ = lean_dbg_trace(v___x_3608_, v___f_3607_);
            crate::leanh::lean_inc(v_a_3594_);
            crate::leanh::lean_inc_ref(v_a_3593_);
            crate::leanh::lean_inc(v_a_3592_);
            crate::leanh::lean_inc_ref(v_a_3591_);
            crate::leanh::lean_inc(v_a_3590_);
            crate::leanh::lean_inc_ref(v_a_3589_);
            crate::leanh::lean_inc(v_a_3588_);
            crate::leanh::lean_inc_ref(v_a_3587_);
            v___x_3610_ = crate::leanh::lean_apply_9(
                v___x_6757__overap_3609_,
                v_a_3587_,
                v_a_3588_,
                v_a_3589_,
                v_a_3590_,
                v_a_3591_,
                v_a_3592_,
                v_a_3593_,
                v_a_3594_,
                crate::leanh::lean_box(0),
            );
            return v___x_3610_;
        } else {
            let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3611_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___closed__0);
            v___x_3612_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_3611_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
            return v___x_3612_;
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1___boxed(
    mut v_x_3613_: *mut crate::leanh::LeanObject,
    mut v_a_3614_: *mut crate::leanh::LeanObject,
    mut v_a_3615_: *mut crate::leanh::LeanObject,
    mut v_a_3616_: *mut crate::leanh::LeanObject,
    mut v_a_3617_: *mut crate::leanh::LeanObject,
    mut v_a_3618_: *mut crate::leanh::LeanObject,
    mut v_a_3619_: *mut crate::leanh::LeanObject,
    mut v_a_3620_: *mut crate::leanh::LeanObject,
    mut v_a_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3623_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1(v_x_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_);
    crate::leanh::lean_dec(v_a_3621_);
    crate::leanh::lean_dec_ref(v_a_3620_);
    crate::leanh::lean_dec(v_a_3619_);
    crate::leanh::lean_dec_ref(v_a_3618_);
    crate::leanh::lean_dec(v_a_3617_);
    crate::leanh::lean_dec_ref(v_a_3616_);
    crate::leanh::lean_dec(v_a_3615_);
    crate::leanh::lean_dec_ref(v_a_3614_);
    return v_res_3623_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(
    mut v_inst_3624_: *mut crate::leanh::LeanObject,
    mut v_a_3625_: *mut crate::leanh::LeanObject,
    mut v___y_3626_: *mut crate::leanh::LeanObject,
    mut v___y_3627_: *mut crate::leanh::LeanObject,
    mut v___y_3628_: *mut crate::leanh::LeanObject,
    mut v___y_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
    mut v___y_3631_: *mut crate::leanh::LeanObject,
    mut v___y_3632_: *mut crate::leanh::LeanObject,
    mut v___y_3633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3635_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___redArg();
    return v___x_3635_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0___boxed(
    mut v_inst_3636_: *mut crate::leanh::LeanObject,
    mut v_a_3637_: *mut crate::leanh::LeanObject,
    mut v___y_3638_: *mut crate::leanh::LeanObject,
    mut v___y_3639_: *mut crate::leanh::LeanObject,
    mut v___y_3640_: *mut crate::leanh::LeanObject,
    mut v___y_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
    mut v___y_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3647_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__1_spec__0(v_inst_3636_, v_a_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
    crate::leanh::lean_dec(v___y_3645_);
    crate::leanh::lean_dec_ref(v___y_3644_);
    crate::leanh::lean_dec(v___y_3643_);
    crate::leanh::lean_dec_ref(v___y_3642_);
    crate::leanh::lean_dec(v___y_3641_);
    crate::leanh::lean_dec_ref(v___y_3640_);
    crate::leanh::lean_dec(v___y_3639_);
    crate::leanh::lean_dec_ref(v___y_3638_);
    return v_res_3647_;
}
pub unsafe fn _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3664_ = l_Lean_Elab_Term_instInhabitedTermElabM(crate::leanh::lean_box(0));
    return v___x_3664_;
}
pub unsafe fn l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(
    mut v_msg_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899__overap_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3673_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0_once), _init_l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___closed__0);
    v___x_5899__overap_3674_ = lean_panic_fn_borrowed(v___x_3673_, v_msg_3665_);
    crate::leanh::lean_inc(v___y_3671_);
    crate::leanh::lean_inc_ref(v___y_3670_);
    crate::leanh::lean_inc(v___y_3669_);
    crate::leanh::lean_inc_ref(v___y_3668_);
    crate::leanh::lean_inc(v___y_3667_);
    crate::leanh::lean_inc_ref(v___y_3666_);
    v___x_3675_ = crate::leanh::lean_apply_7(
        v___x_5899__overap_3674_,
        v___y_3666_,
        v___y_3667_,
        v___y_3668_,
        v___y_3669_,
        v___y_3670_,
        v___y_3671_,
        crate::leanh::lean_box(0),
    );
    return v___x_3675_;
}
pub unsafe fn l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2___boxed(
    mut v_msg_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
    mut v___y_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3684_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v_msg_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
    crate::leanh::lean_dec(v___y_3682_);
    crate::leanh::lean_dec_ref(v___y_3681_);
    crate::leanh::lean_dec(v___y_3680_);
    crate::leanh::lean_dec_ref(v___y_3679_);
    crate::leanh::lean_dec(v___y_3678_);
    crate::leanh::lean_dec_ref(v___y_3677_);
    return v_res_3684_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(
    mut v_ref_3685_: *mut crate::leanh::LeanObject,
    mut v_msgData_3686_: *mut crate::leanh::LeanObject,
    mut v_severity_3687_: u8,
    mut v_isSilent_3688_: u8,
    mut v___y_3689_: *mut crate::leanh::LeanObject,
    mut v___y_3690_: *mut crate::leanh::LeanObject,
    mut v___y_3691_: *mut crate::leanh::LeanObject,
    mut v___y_3692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3699_: u8 = 0;
    let mut v___y_3700_: u8 = 0;
    let mut v___y_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3718_: u8 = 0;
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut v___y_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3733_: u8 = 0;
    let mut v___y_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: u8 = 0;
    let mut v___y_3737_: u8 = 0;
    let mut v___y_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3744_: u8 = 0;
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut v___y_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3758_: u8 = 0;
    let mut v___y_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3760_: u8 = 0;
    let mut v___y_3761_: u8 = 0;
    let mut v___y_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: u8 = 0;
    let mut v___y_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3772_: u8 = 0;
    let mut v___y_3773_: u8 = 0;
    let mut v_ref_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: u8 = 0;
    let mut v___y_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3781_: u8 = 0;
    let mut v___y_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3785_: u8 = 0;
    let mut v___y_3786_: u8 = 0;
    let mut v___y_3788_: u8 = 0;
    let mut v_fileName_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3793_: u8 = 0;
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: u8 = 0;
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: u8 = 0;
    let mut v___x_3804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3778_ = 2;
                v___x_3803_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3687_, v___x_3778_);
                if v___x_3803_ == 0 {
                    v___y_3788_ = v___x_3803_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_3686_);
                    v___x_3804_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3686_);
                    v___y_3788_ = v___x_3804_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3704_ = lean_st_ref_take(v___y_3703_);
                v_currNamespace_3705_ = crate::leanh::lean_ctor_get(v___y_3702_, 6);
                v_openDecls_3706_ = crate::leanh::lean_ctor_get(v___y_3702_, 7);
                v_env_3707_ = crate::leanh::lean_ctor_get(v___x_3704_, 0);
                v_nextMacroScope_3708_ = crate::leanh::lean_ctor_get(v___x_3704_, 1);
                v_ngen_3709_ = crate::leanh::lean_ctor_get(v___x_3704_, 2);
                v_auxDeclNGen_3710_ = crate::leanh::lean_ctor_get(v___x_3704_, 3);
                v_traceState_3711_ = crate::leanh::lean_ctor_get(v___x_3704_, 4);
                v_cache_3712_ = crate::leanh::lean_ctor_get(v___x_3704_, 5);
                v_messages_3713_ = crate::leanh::lean_ctor_get(v___x_3704_, 6);
                v_infoState_3714_ = crate::leanh::lean_ctor_get(v___x_3704_, 7);
                v_snapshotTasks_3715_ = crate::leanh::lean_ctor_get(v___x_3704_, 8);
                v_isSharedCheck_3729_ = (!crate::leanh::lean_is_exclusive(v___x_3704_)) as u8;
                if v_isSharedCheck_3729_ == 0 {
                    v___x_3717_ = v___x_3704_;
                    v_isShared_3718_ = v_isSharedCheck_3729_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3715_);
                    crate::leanh::lean_inc(v_infoState_3714_);
                    crate::leanh::lean_inc(v_messages_3713_);
                    crate::leanh::lean_inc(v_cache_3712_);
                    crate::leanh::lean_inc(v_traceState_3711_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3710_);
                    crate::leanh::lean_inc(v_ngen_3709_);
                    crate::leanh::lean_inc(v_nextMacroScope_3708_);
                    crate::leanh::lean_inc(v_env_3707_);
                    crate::leanh::lean_dec(v___x_3704_);
                    v___x_3717_ = crate::leanh::lean_box(0);
                    v_isShared_3718_ = v_isSharedCheck_3729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_3706_);
                crate::leanh::lean_inc(v_currNamespace_3705_);
                v___x_3719_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3719_, 0, v_currNamespace_3705_);
                crate::leanh::lean_ctor_set(v___x_3719_, 1, v_openDecls_3706_);
                v___x_3720_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3720_, 0, v___x_3719_);
                crate::leanh::lean_ctor_set(v___x_3720_, 1, v___y_3696_);
                crate::leanh::lean_inc_ref(v___y_3701_);
                crate::leanh::lean_inc_ref(v___y_3695_);
                v___x_3721_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_3721_, 0, v___y_3695_);
                crate::leanh::lean_ctor_set(v___x_3721_, 1, v___y_3697_);
                crate::leanh::lean_ctor_set(v___x_3721_, 2, v___y_3698_);
                crate::leanh::lean_ctor_set(v___x_3721_, 3, v___y_3701_);
                crate::leanh::lean_ctor_set(v___x_3721_, 4, v___x_3720_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3721_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_3699_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3721_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_3700_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3721_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3688_,
                );
                v___x_3722_ = l_Lean_MessageLog_add(v___x_3721_, v_messages_3713_);
                if v_isShared_3718_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3717_, 6, v___x_3722_);
                    v___x_3724_ = v___x_3717_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3728_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_env_3707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_nextMacroScope_3708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 2, v_ngen_3709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 3, v_auxDeclNGen_3710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 4, v_traceState_3711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 5, v_cache_3712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 6, v___x_3722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 7, v_infoState_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 8, v_snapshotTasks_3715_);
                    v___x_3724_ = v_reuseFailAlloc_3728_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3725_ = lean_st_ref_set(v___y_3703_, v___x_3724_);
                v___x_3726_ = crate::leanh::lean_box(0);
                v___x_3727_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3727_, 0, v___x_3726_);
                return v___x_3727_;
            }
            4 => {
                v___x_3739_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3686_,
                    );
                v___x_3740_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__4(v___x_3739_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
                v_a_3741_ = crate::leanh::lean_ctor_get(v___x_3740_, 0);
                v_isSharedCheck_3754_ = (!crate::leanh::lean_is_exclusive(v___x_3740_)) as u8;
                if v_isSharedCheck_3754_ == 0 {
                    v___x_3743_ = v___x_3740_;
                    v_isShared_3744_ = v_isSharedCheck_3754_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3741_);
                    crate::leanh::lean_dec(v___x_3740_);
                    v___x_3743_ = crate::leanh::lean_box(0);
                    v_isShared_3744_ = v_isSharedCheck_3754_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_3732_, 2);
                v___x_3745_ = l_Lean_FileMap_toPosition(v___y_3732_, v___y_3735_);
                crate::leanh::lean_dec(v___y_3735_);
                v___x_3746_ = l_Lean_FileMap_toPosition(v___y_3732_, v___y_3738_);
                crate::leanh::lean_dec(v___y_3738_);
                v___x_3747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3747_, 0, v___x_3746_);
                v___x_3748_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0;
                if v___y_3733_ == 0 {
                    crate::leanh::lean_del_object(v___x_3743_);
                    crate::leanh::lean_dec_ref(v___y_3731_);
                    v___y_3695_ = v___y_3734_;
                    v___y_3696_ = v_a_3741_;
                    v___y_3697_ = v___x_3745_;
                    v___y_3698_ = v___x_3747_;
                    v___y_3699_ = v___y_3736_;
                    v___y_3700_ = v___y_3737_;
                    v___y_3701_ = v___x_3748_;
                    v___y_3702_ = v___y_3691_;
                    v___y_3703_ = v___y_3692_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3741_);
                    v___x_3749_ = l_Lean_MessageData_hasTag(v___y_3731_, v_a_3741_);
                    if v___x_3749_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3747_, 1);
                        crate::leanh::lean_dec_ref(v___x_3745_);
                        crate::leanh::lean_dec(v_a_3741_);
                        v___x_3750_ = crate::leanh::lean_box(0);
                        if v_isShared_3744_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3743_, 0, v___x_3750_);
                            v___x_3752_ = v___x_3743_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3753_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
                            v___x_3752_ = v_reuseFailAlloc_3753_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3743_);
                        v___y_3695_ = v___y_3734_;
                        v___y_3696_ = v_a_3741_;
                        v___y_3697_ = v___x_3745_;
                        v___y_3698_ = v___x_3747_;
                        v___y_3699_ = v___y_3736_;
                        v___y_3700_ = v___y_3737_;
                        v___y_3701_ = v___x_3748_;
                        v___y_3702_ = v___y_3691_;
                        v___y_3703_ = v___y_3692_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3752_;
            }
            7 => {
                v___x_3764_ = l_Lean_Syntax_getTailPos_x3f(v___y_3762_, v___y_3760_);
                crate::leanh::lean_dec(v___y_3762_);
                if crate::leanh::lean_obj_tag(v___x_3764_) == 0 {
                    crate::leanh::lean_inc(v___y_3763_);
                    v___y_3731_ = v___y_3756_;
                    v___y_3732_ = v___y_3757_;
                    v___y_3733_ = v___y_3758_;
                    v___y_3734_ = v___y_3759_;
                    v___y_3735_ = v___y_3763_;
                    v___y_3736_ = v___y_3760_;
                    v___y_3737_ = v___y_3761_;
                    v___y_3738_ = v___y_3763_;
                    state = 4;
                    continue;
                } else {
                    v_val_3765_ = crate::leanh::lean_ctor_get(v___x_3764_, 0);
                    crate::leanh::lean_inc(v_val_3765_);
                    crate::leanh::lean_dec_ref_known(v___x_3764_, 1);
                    v___y_3731_ = v___y_3756_;
                    v___y_3732_ = v___y_3757_;
                    v___y_3733_ = v___y_3758_;
                    v___y_3734_ = v___y_3759_;
                    v___y_3735_ = v___y_3763_;
                    v___y_3736_ = v___y_3760_;
                    v___y_3737_ = v___y_3761_;
                    v___y_3738_ = v_val_3765_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_3774_ = l_Lean_replaceRef(v_ref_3685_, v___y_3771_);
                v___x_3775_ = l_Lean_Syntax_getPos_x3f(v_ref_3774_, v___y_3772_);
                if crate::leanh::lean_obj_tag(v___x_3775_) == 0 {
                    v___x_3776_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3756_ = v___y_3767_;
                    v___y_3757_ = v___y_3768_;
                    v___y_3758_ = v___y_3769_;
                    v___y_3759_ = v___y_3770_;
                    v___y_3760_ = v___y_3772_;
                    v___y_3761_ = v___y_3773_;
                    v___y_3762_ = v_ref_3774_;
                    v___y_3763_ = v___x_3776_;
                    state = 7;
                    continue;
                } else {
                    v_val_3777_ = crate::leanh::lean_ctor_get(v___x_3775_, 0);
                    crate::leanh::lean_inc(v_val_3777_);
                    crate::leanh::lean_dec_ref_known(v___x_3775_, 1);
                    v___y_3756_ = v___y_3767_;
                    v___y_3757_ = v___y_3768_;
                    v___y_3758_ = v___y_3769_;
                    v___y_3759_ = v___y_3770_;
                    v___y_3760_ = v___y_3772_;
                    v___y_3761_ = v___y_3773_;
                    v___y_3762_ = v_ref_3774_;
                    v___y_3763_ = v_val_3777_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3786_ == 0 {
                    v___y_3767_ = v___y_3784_;
                    v___y_3768_ = v___y_3780_;
                    v___y_3769_ = v___y_3781_;
                    v___y_3770_ = v___y_3782_;
                    v___y_3771_ = v___y_3783_;
                    v___y_3772_ = v___y_3785_;
                    v___y_3773_ = v_severity_3687_;
                    state = 8;
                    continue;
                } else {
                    v___y_3767_ = v___y_3784_;
                    v___y_3768_ = v___y_3780_;
                    v___y_3769_ = v___y_3781_;
                    v___y_3770_ = v___y_3782_;
                    v___y_3771_ = v___y_3783_;
                    v___y_3772_ = v___y_3785_;
                    v___y_3773_ = v___x_3778_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3788_ == 0 {
                    v_fileName_3789_ = crate::leanh::lean_ctor_get(v___y_3691_, 0);
                    v_fileMap_3790_ = crate::leanh::lean_ctor_get(v___y_3691_, 1);
                    v_options_3791_ = crate::leanh::lean_ctor_get(v___y_3691_, 2);
                    v_ref_3792_ = crate::leanh::lean_ctor_get(v___y_3691_, 5);
                    v_suppressElabErrors_3793_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3691_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3794_ = crate::leanh::lean_box((v___y_3788_) as usize);
                    v___x_3795_ = crate::leanh::lean_box((v_suppressElabErrors_3793_) as usize);
                    v___f_3796_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_3796_, 0, v___x_3794_);
                    crate::leanh::lean_closure_set(v___f_3796_, 1, v___x_3795_);
                    v___x_3797_ = 1;
                    v___x_3798_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3687_, v___x_3797_);
                    if v___x_3798_ == 0 {
                        v___y_3780_ = v_fileMap_3790_;
                        v___y_3781_ = v_suppressElabErrors_3793_;
                        v___y_3782_ = v_fileName_3789_;
                        v___y_3783_ = v_ref_3792_;
                        v___y_3784_ = v___f_3796_;
                        v___y_3785_ = v___y_3788_;
                        v___y_3786_ = v___x_3798_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3799_ = l_Lean_warningAsError;
                        v___x_3800_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_3791_, v___x_3799_);
                        v___y_3780_ = v_fileMap_3790_;
                        v___y_3781_ = v_suppressElabErrors_3793_;
                        v___y_3782_ = v_fileName_3789_;
                        v___y_3783_ = v_ref_3792_;
                        v___y_3784_ = v___f_3796_;
                        v___y_3785_ = v___y_3788_;
                        v___y_3786_ = v___x_3800_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_3686_);
                    v___x_3801_ = crate::leanh::lean_box(0);
                    v___x_3802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3802_, 0, v___x_3801_);
                    return v___x_3802_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg___boxed(
    mut v_ref_3805_: *mut crate::leanh::LeanObject,
    mut v_msgData_3806_: *mut crate::leanh::LeanObject,
    mut v_severity_3807_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3808_: *mut crate::leanh::LeanObject,
    mut v___y_3809_: *mut crate::leanh::LeanObject,
    mut v___y_3810_: *mut crate::leanh::LeanObject,
    mut v___y_3811_: *mut crate::leanh::LeanObject,
    mut v___y_3812_: *mut crate::leanh::LeanObject,
    mut v___y_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3814_: u8 = 0;
    let mut v_isSilent_boxed_3815_: u8 = 0;
    let mut v_res_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3814_ = (crate::leanh::lean_unbox(v_severity_3807_) as u8);
    v_isSilent_boxed_3815_ = (crate::leanh::lean_unbox(v_isSilent_3808_) as u8);
    v_res_3816_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_3805_, v_msgData_3806_, v_severity_boxed_3814_, v_isSilent_boxed_3815_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
    crate::leanh::lean_dec(v___y_3812_);
    crate::leanh::lean_dec_ref(v___y_3811_);
    crate::leanh::lean_dec(v___y_3810_);
    crate::leanh::lean_dec_ref(v___y_3809_);
    crate::leanh::lean_dec(v_ref_3805_);
    return v_res_3816_;
}
pub unsafe fn l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(
    mut v_msgData_3817_: *mut crate::leanh::LeanObject,
    mut v_severity_3818_: u8,
    mut v_isSilent_3819_: u8,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
    mut v___y_3821_: *mut crate::leanh::LeanObject,
    mut v___y_3822_: *mut crate::leanh::LeanObject,
    mut v___y_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3827_ = crate::leanh::lean_ctor_get(v___y_3824_, 5);
    v___x_3828_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_3827_, v_msgData_3817_, v_severity_3818_, v_isSilent_3819_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
    return v___x_3828_;
}
pub unsafe fn l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1___boxed(
    mut v_msgData_3829_: *mut crate::leanh::LeanObject,
    mut v_severity_3830_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
    mut v___y_3835_: *mut crate::leanh::LeanObject,
    mut v___y_3836_: *mut crate::leanh::LeanObject,
    mut v___y_3837_: *mut crate::leanh::LeanObject,
    mut v___y_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3839_: u8 = 0;
    let mut v_isSilent_boxed_3840_: u8 = 0;
    let mut v_res_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3839_ = (crate::leanh::lean_unbox(v_severity_3830_) as u8);
    v_isSilent_boxed_3840_ = (crate::leanh::lean_unbox(v_isSilent_3831_) as u8);
    v_res_3841_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v_msgData_3829_, v_severity_boxed_3839_, v_isSilent_boxed_3840_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
    crate::leanh::lean_dec(v___y_3837_);
    crate::leanh::lean_dec_ref(v___y_3836_);
    crate::leanh::lean_dec(v___y_3835_);
    crate::leanh::lean_dec_ref(v___y_3834_);
    crate::leanh::lean_dec(v___y_3833_);
    crate::leanh::lean_dec_ref(v___y_3832_);
    return v_res_3841_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: u8 = 0;
    let mut v___x_3845_: u32 = 0;
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3843_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
                v___x_3844_ = l_IO_CancelToken_isSet(v___x_3843_);
                crate::leanh::lean_dec_ref(v___x_3843_);
                if v___x_3844_ == 0 {
                    v___x_3845_ = 30;
                    v___x_3846_ = l_IO_sleep(v___x_3845_);
                    state = 0;
                    continue;
                } else {
                    v___x_3848_ = crate::leanh::lean_box(0);
                    v___x_3849_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3849_, 0, v___x_3848_);
                    return v___x_3849_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg___boxed(
    mut v___y_3850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3851_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
    return v_res_3851_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
    v___x_3854_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_3855_ = crate::leanh::lean_unsigned_to_nat(113);
    v___x_3856_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__0;
    v___x_3857_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10;
    v___x_3858_ = l_mkPanicMessageWithDecl(
        v___x_3857_,
        v___x_3856_,
        v___x_3855_,
        v___x_3854_,
        v___x_3853_,
    );
    return v___x_3858_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(
    mut v_x_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
    mut v___y_3862_: *mut crate::leanh::LeanObject,
    mut v___y_3863_: *mut crate::leanh::LeanObject,
    mut v___y_3864_: *mut crate::leanh::LeanObject,
    mut v___y_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancelTk_x3f_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3873_: u8 = 0;
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: u8 = 0;
    let mut v___x_3883_: u8 = 0;
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3888_: u8 = 0;
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut v_unused_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cancelTk_x3f_3867_ = crate::leanh::lean_ctor_get(v___y_3864_, 12);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_3867_) == 1 {
                    v_ref_3868_ = crate::leanh::lean_ctor_get(v___y_3864_, 5);
                    v_val_3869_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_3867_, 0);
                    v___x_3870_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
                    if crate::leanh::lean_obj_tag(v___x_3870_) == 0 {
                        v_isSharedCheck_3897_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3870_)) as u8;
                        if v_isSharedCheck_3897_ == 0 {
                            v_unused_3898_ = crate::leanh::lean_ctor_get(v___x_3870_, 0);
                            crate::leanh::lean_dec(v_unused_3898_);
                            v___x_3872_ = v___x_3870_;
                            v_isShared_3873_ = v_isSharedCheck_3897_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3870_);
                            v___x_3872_ = crate::leanh::lean_box(0);
                            v_isShared_3873_ = v_isSharedCheck_3897_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3870_;
                    }
                } else {
                    v___x_3899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___closed__1);
                    v___x_3900_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_3899_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
                    return v___x_3900_;
                }
            }
            1 => {
                v___x_3874_ = l_IO_CancelToken_isSet(v_val_3869_);
                if v___x_3874_ == 0 {
                    v___x_3875_ = crate::leanh::lean_box(0);
                    if v_isShared_3873_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3872_, 0, v___x_3875_);
                        v___x_3877_ = v___x_3872_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
                        v___x_3877_ = v_reuseFailAlloc_3878_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3872_);
                    v___x_3879_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6;
                    v___x_3880_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_3879_);
                    if crate::leanh::lean_obj_tag(v___x_3880_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3880_, 1);
                        v___x_3881_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
                        v___x_3882_ = 2;
                        v___x_3883_ = 0;
                        v___x_3884_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_3881_, v___x_3882_, v___x_3883_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
                        return v___x_3884_;
                    } else {
                        v_a_3885_ = crate::leanh::lean_ctor_get(v___x_3880_, 0);
                        v_isSharedCheck_3896_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3880_)) as u8;
                        if v_isSharedCheck_3896_ == 0 {
                            v___x_3887_ = v___x_3880_;
                            v_isShared_3888_ = v_isSharedCheck_3896_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3885_);
                            crate::leanh::lean_dec(v___x_3880_);
                            v___x_3887_ = crate::leanh::lean_box(0);
                            v_isShared_3888_ = v_isSharedCheck_3896_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3877_;
            }
            3 => {
                v___x_3889_ = lean_io_error_to_string(v_a_3885_);
                v___x_3890_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3890_, 0, v___x_3889_);
                v___x_3891_ = l_Lean_MessageData_ofFormat(v___x_3890_);
                crate::leanh::lean_inc(v_ref_3868_);
                v___x_3892_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3892_, 0, v_ref_3868_);
                crate::leanh::lean_ctor_set(v___x_3892_, 1, v___x_3891_);
                if v_isShared_3888_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3887_, 0, v___x_3892_);
                    v___x_3894_ = v___x_3887_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3892_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0___boxed(
    mut v_x_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
    mut v___y_3903_: *mut crate::leanh::LeanObject,
    mut v___y_3904_: *mut crate::leanh::LeanObject,
    mut v___y_3905_: *mut crate::leanh::LeanObject,
    mut v___y_3906_: *mut crate::leanh::LeanObject,
    mut v___y_3907_: *mut crate::leanh::LeanObject,
    mut v___y_3908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___lam__0(v_x_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
    crate::leanh::lean_dec(v___y_3907_);
    crate::leanh::lean_dec_ref(v___y_3906_);
    crate::leanh::lean_dec(v___y_3905_);
    crate::leanh::lean_dec_ref(v___y_3904_);
    crate::leanh::lean_dec(v___y_3903_);
    crate::leanh::lean_dec_ref(v___y_3902_);
    return v_res_3909_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3918_ = crate::leanh::lean_box(0);
    v___x_3919_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3918_);
    return v___x_3919_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(
    mut v_x_3920_: *mut crate::leanh::LeanObject,
    mut v_a_3921_: *mut crate::leanh::LeanObject,
    mut v_a_3922_: *mut crate::leanh::LeanObject,
    mut v_a_3923_: *mut crate::leanh::LeanObject,
    mut v_a_3924_: *mut crate::leanh::LeanObject,
    mut v_a_3925_: *mut crate::leanh::LeanObject,
    mut v_a_3926_: *mut crate::leanh::LeanObject,
    mut v_a_3927_: *mut crate::leanh::LeanObject,
    mut v_a_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: u8 = 0;
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3930_ = l_Lean_Server_Test_Cancel_tacticWait__for__unblock__async___closed__1;
                v___x_3931_ = l_Lean_Syntax_isOfKind(v_x_3920_, v___x_3930_);
                if v___x_3931_ == 0 {
                    v___x_3932_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
                    return v___x_3932_;
                } else {
                    v___x_3933_ = l_IO_CancelToken_new();
                    v___f_3934_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__0;
                    v___x_3935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3935_, 0, v___x_3933_);
                    v___x_3936_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__2;
                    v___x_3937_ = l_Lean_Name_toString(v___x_3936_, v___x_3931_);
                    crate::leanh::lean_inc_ref(v___x_3935_);
                    v___x_3938_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(
                        v___f_3934_,
                        v___x_3935_,
                        v___x_3937_,
                        v_a_3923_,
                        v_a_3924_,
                        v_a_3925_,
                        v_a_3926_,
                        v_a_3927_,
                        v_a_3928_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3938_) == 0 {
                        v_a_3939_ = crate::leanh::lean_ctor_get(v___x_3938_, 0);
                        crate::leanh::lean_inc(v_a_3939_);
                        crate::leanh::lean_dec_ref_known(v___x_3938_, 1);
                        v___x_3940_ = crate::leanh::lean_box(0);
                        v___x_3941_ = crate::leanh::lean_apply_1(v_a_3939_, v___x_3940_);
                        v___x_3942_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3943_ = lean_io_as_task(v___x_3941_, v___x_3942_);
                        v___x_3944_ = crate::leanh::lean_box(0);
                        v___x_3945_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
                        v___x_3946_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3946_, 0, v___x_3944_);
                        crate::leanh::lean_ctor_set(v___x_3946_, 1, v___x_3945_);
                        crate::leanh::lean_ctor_set(v___x_3946_, 2, v___x_3935_);
                        crate::leanh::lean_ctor_set(v___x_3946_, 3, v___x_3943_);
                        v___x_3947_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3946_, v_a_3928_);
                        if crate::leanh::lean_obj_tag(v___x_3947_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3947_, 1);
                            v___x_3948_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
                            v___x_3949_ = 2;
                            v___x_3950_ = 0;
                            v___x_3951_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_3948_, v___x_3949_, v___x_3950_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
                            return v___x_3951_;
                        } else {
                            return v___x_3947_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_3935_, 1);
                        v_a_3952_ = crate::leanh::lean_ctor_get(v___x_3938_, 0);
                        v_isSharedCheck_3959_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3938_)) as u8;
                        if v_isSharedCheck_3959_ == 0 {
                            v___x_3954_ = v___x_3938_;
                            v_isShared_3955_ = v_isSharedCheck_3959_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3952_);
                            crate::leanh::lean_dec(v___x_3938_);
                            v___x_3954_ = crate::leanh::lean_box(0);
                            v_isShared_3955_ = v_isSharedCheck_3959_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3955_ == 0 {
                    v___x_3957_ = v___x_3954_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
                    v___x_3957_ = v_reuseFailAlloc_3958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___boxed(
    mut v_x_3960_: *mut crate::leanh::LeanObject,
    mut v_a_3961_: *mut crate::leanh::LeanObject,
    mut v_a_3962_: *mut crate::leanh::LeanObject,
    mut v_a_3963_: *mut crate::leanh::LeanObject,
    mut v_a_3964_: *mut crate::leanh::LeanObject,
    mut v_a_3965_: *mut crate::leanh::LeanObject,
    mut v_a_3966_: *mut crate::leanh::LeanObject,
    mut v_a_3967_: *mut crate::leanh::LeanObject,
    mut v_a_3968_: *mut crate::leanh::LeanObject,
    mut v_a_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1(v_x_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
    crate::leanh::lean_dec(v_a_3968_);
    crate::leanh::lean_dec_ref(v_a_3967_);
    crate::leanh::lean_dec(v_a_3966_);
    crate::leanh::lean_dec_ref(v_a_3965_);
    crate::leanh::lean_dec(v_a_3964_);
    crate::leanh::lean_dec_ref(v_a_3963_);
    crate::leanh::lean_dec(v_a_3962_);
    crate::leanh::lean_dec_ref(v_a_3961_);
    return v_res_3970_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(
    mut v_inst_3971_: *mut crate::leanh::LeanObject,
    mut v_a_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3980_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___redArg();
    return v___x_3980_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0___boxed(
    mut v_inst_3981_: *mut crate::leanh::LeanObject,
    mut v_a_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
    mut v___y_3987_: *mut crate::leanh::LeanObject,
    mut v___y_3988_: *mut crate::leanh::LeanObject,
    mut v___y_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3990_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__0(v_inst_3981_, v_a_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
    crate::leanh::lean_dec(v___y_3988_);
    crate::leanh::lean_dec_ref(v___y_3987_);
    crate::leanh::lean_dec(v___y_3986_);
    crate::leanh::lean_dec_ref(v___y_3985_);
    crate::leanh::lean_dec(v___y_3984_);
    crate::leanh::lean_dec_ref(v___y_3983_);
    return v_res_3990_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(
    mut v_ref_3991_: *mut crate::leanh::LeanObject,
    mut v_msgData_3992_: *mut crate::leanh::LeanObject,
    mut v_severity_3993_: u8,
    mut v_isSilent_3994_: u8,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
    mut v___y_3996_: *mut crate::leanh::LeanObject,
    mut v___y_3997_: *mut crate::leanh::LeanObject,
    mut v___y_3998_: *mut crate::leanh::LeanObject,
    mut v___y_3999_: *mut crate::leanh::LeanObject,
    mut v___y_4000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4002_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___redArg(v_ref_3991_, v_msgData_3992_, v_severity_3993_, v_isSilent_3994_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
    return v___x_4002_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1___boxed(
    mut v_ref_4003_: *mut crate::leanh::LeanObject,
    mut v_msgData_4004_: *mut crate::leanh::LeanObject,
    mut v_severity_4005_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4014_: u8 = 0;
    let mut v_isSilent_boxed_4015_: u8 = 0;
    let mut v_res_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4014_ = (crate::leanh::lean_unbox(v_severity_4005_) as u8);
    v_isSilent_boxed_4015_ = (crate::leanh::lean_unbox(v_isSilent_4006_) as u8);
    v_res_4016_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1_spec__1(v_ref_4003_, v_msgData_4004_, v_severity_boxed_4014_, v_isSilent_boxed_4015_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
    crate::leanh::lean_dec(v___y_4012_);
    crate::leanh::lean_dec_ref(v___y_4011_);
    crate::leanh::lean_dec(v___y_4010_);
    crate::leanh::lean_dec_ref(v___y_4009_);
    crate::leanh::lean_dec(v___y_4008_);
    crate::leanh::lean_dec_ref(v___y_4007_);
    crate::leanh::lean_dec(v_ref_4003_);
    return v_res_4016_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(
    mut v_x_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
    mut v___y_4036_: *mut crate::leanh::LeanObject,
    mut v___y_4037_: *mut crate::leanh::LeanObject,
    mut v___y_4038_: *mut crate::leanh::LeanObject,
    mut v___y_4039_: *mut crate::leanh::LeanObject,
    mut v___y_4040_: *mut crate::leanh::LeanObject,
    mut v___y_4041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4043_ =
        l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_getUnblockedCancelTk();
    v___x_4044_ = l_IO_CancelToken_set(v___x_4043_);
    crate::leanh::lean_dec_ref(v___x_4043_);
    v___x_4045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4045_, 0, v___x_4044_);
    return v___x_4045_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0___boxed(
    mut v_x_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
    mut v___y_4049_: *mut crate::leanh::LeanObject,
    mut v___y_4050_: *mut crate::leanh::LeanObject,
    mut v___y_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4056_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___lam__0(v_x_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
    crate::leanh::lean_dec(v___y_4054_);
    crate::leanh::lean_dec_ref(v___y_4053_);
    crate::leanh::lean_dec(v___y_4052_);
    crate::leanh::lean_dec_ref(v___y_4051_);
    crate::leanh::lean_dec(v___y_4050_);
    crate::leanh::lean_dec_ref(v___y_4049_);
    crate::leanh::lean_dec(v___y_4048_);
    crate::leanh::lean_dec_ref(v___y_4047_);
    return v_res_4056_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(
    mut v_x_4059_: *mut crate::leanh::LeanObject,
    mut v_a_4060_: *mut crate::leanh::LeanObject,
    mut v_a_4061_: *mut crate::leanh::LeanObject,
    mut v_a_4062_: *mut crate::leanh::LeanObject,
    mut v_a_4063_: *mut crate::leanh::LeanObject,
    mut v_a_4064_: *mut crate::leanh::LeanObject,
    mut v_a_4065_: *mut crate::leanh::LeanObject,
    mut v_a_4066_: *mut crate::leanh::LeanObject,
    mut v_a_4067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    v___x_4069_ = l_Lean_Server_Test_Cancel_tacticUnblock___closed__1;
    v___x_4070_ = l_Lean_Syntax_isOfKind(v_x_4059_, v___x_4069_);
    if v___x_4070_ == 0 {
        let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
        return v___x_4071_;
    } else {
        let mut v___f_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_789__overap_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4072_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__0;
        v___x_4073_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___closed__1;
        v___x_789__overap_4074_ = lean_dbg_trace(v___x_4073_, v___f_4072_);
        crate::leanh::lean_inc(v_a_4067_);
        crate::leanh::lean_inc_ref(v_a_4066_);
        crate::leanh::lean_inc(v_a_4065_);
        crate::leanh::lean_inc_ref(v_a_4064_);
        crate::leanh::lean_inc(v_a_4063_);
        crate::leanh::lean_inc_ref(v_a_4062_);
        crate::leanh::lean_inc(v_a_4061_);
        crate::leanh::lean_inc_ref(v_a_4060_);
        v___x_4075_ = crate::leanh::lean_apply_9(
            v___x_789__overap_4074_,
            v_a_4060_,
            v_a_4061_,
            v_a_4062_,
            v_a_4063_,
            v_a_4064_,
            v_a_4065_,
            v_a_4066_,
            v_a_4067_,
            crate::leanh::lean_box(0),
        );
        return v___x_4075_;
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1___boxed(
    mut v_x_4076_: *mut crate::leanh::LeanObject,
    mut v_a_4077_: *mut crate::leanh::LeanObject,
    mut v_a_4078_: *mut crate::leanh::LeanObject,
    mut v_a_4079_: *mut crate::leanh::LeanObject,
    mut v_a_4080_: *mut crate::leanh::LeanObject,
    mut v_a_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
    mut v_a_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4086_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticUnblock__1(v_x_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
    crate::leanh::lean_dec(v_a_4084_);
    crate::leanh::lean_dec_ref(v_a_4083_);
    crate::leanh::lean_dec(v_a_4082_);
    crate::leanh::lean_dec_ref(v_a_4081_);
    crate::leanh::lean_dec(v_a_4080_);
    crate::leanh::lean_dec_ref(v_a_4079_);
    crate::leanh::lean_dec(v_a_4078_);
    crate::leanh::lean_dec_ref(v_a_4077_);
    return v_res_4086_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(
    mut v_x_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: u8 = 0;
    let mut v___x_4115_: u8 = 0;
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4113_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
    v___x_4114_ = 2;
    v___x_4115_ = 0;
    v___x_4116_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1(v___x_4113_, v___x_4114_, v___x_4115_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
    return v___x_4116_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0___boxed(
    mut v_x_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__0(v_x_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
    crate::leanh::lean_dec(v___y_4125_);
    crate::leanh::lean_dec_ref(v___y_4124_);
    crate::leanh::lean_dec(v___y_4123_);
    crate::leanh::lean_dec_ref(v___y_4122_);
    crate::leanh::lean_dec(v___y_4121_);
    crate::leanh::lean_dec_ref(v___y_4120_);
    crate::leanh::lean_dec(v___y_4119_);
    crate::leanh::lean_dec_ref(v___y_4118_);
    return v_res_4127_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(
    mut v_val_4128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4130_: u8 = 0;
    let mut v___x_4131_: u32 = 0;
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4130_ = l_IO_CancelToken_isSet(v_val_4128_);
                if v___x_4130_ == 0 {
                    v___x_4131_ = 30;
                    v___x_4132_ = l_IO_sleep(v___x_4131_);
                    state = 0;
                    continue;
                } else {
                    v___x_4134_ = crate::leanh::lean_box(0);
                    v___x_4135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4135_, 0, v___x_4134_);
                    return v___x_4135_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg___boxed(
    mut v_val_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4138_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_4136_);
    crate::leanh::lean_dec_ref(v_val_4136_);
    return v_res_4138_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
    v___x_4141_ = crate::leanh::lean_unsigned_to_nat(41);
    v___x_4142_ = crate::leanh::lean_unsigned_to_nat(147);
    v___x_4143_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__0;
    v___x_4144_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10;
    v___x_4145_ = l_mkPanicMessageWithDecl(
        v___x_4144_,
        v___x_4143_,
        v___x_4142_,
        v___x_4141_,
        v___x_4140_,
    );
    return v___x_4145_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(
    mut v_val_4146_: *mut crate::leanh::LeanObject,
    mut v_x_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cancelTk_x3f_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4161_: u8 = 0;
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: u8 = 0;
    let mut v___x_4166_: u8 = 0;
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4170_: u8 = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4178_: u8 = 0;
    let mut v_unused_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4183_: u8 = 0;
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4193_: u8 = 0;
    let mut v_isSharedCheck_4194_: u8 = 0;
    let mut v_unused_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cancelTk_x3f_4155_ = crate::leanh::lean_ctor_get(v___y_4152_, 12);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_4155_) == 1 {
                    v_ref_4156_ = crate::leanh::lean_ctor_get(v___y_4152_, 5);
                    v_val_4157_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_4155_, 0);
                    v___x_4158_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_4157_);
                    if crate::leanh::lean_obj_tag(v___x_4158_) == 0 {
                        v_isSharedCheck_4194_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4158_)) as u8;
                        if v_isSharedCheck_4194_ == 0 {
                            v_unused_4195_ = crate::leanh::lean_ctor_get(v___x_4158_, 0);
                            crate::leanh::lean_dec(v_unused_4195_);
                            v___x_4160_ = v___x_4158_;
                            v_isShared_4161_ = v_isSharedCheck_4194_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4158_);
                            v___x_4160_ = crate::leanh::lean_box(0);
                            v_isShared_4161_ = v_isSharedCheck_4194_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_4158_;
                    }
                } else {
                    v___x_4196_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___closed__1);
                    v___x_4197_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__2(v___x_4196_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
                    return v___x_4197_;
                }
            }
            1 => {
                v___x_4162_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6;
                v___x_4163_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_4162_);
                if crate::leanh::lean_obj_tag(v___x_4163_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4163_, 1);
                    crate::leanh::lean_del_object(v___x_4160_);
                    v___x_4164_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
                    v___x_4165_ = 2;
                    v___x_4166_ = 0;
                    v___x_4167_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_4164_, v___x_4165_, v___x_4166_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
                    if crate::leanh::lean_obj_tag(v___x_4167_) == 0 {
                        v_isSharedCheck_4178_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4167_)) as u8;
                        if v_isSharedCheck_4178_ == 0 {
                            v_unused_4179_ = crate::leanh::lean_ctor_get(v___x_4167_, 0);
                            crate::leanh::lean_dec(v_unused_4179_);
                            v___x_4169_ = v___x_4167_;
                            v_isShared_4170_ = v_isSharedCheck_4178_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4167_);
                            v___x_4169_ = crate::leanh::lean_box(0);
                            v_isShared_4170_ = v_isSharedCheck_4178_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_4167_;
                    }
                } else {
                    v_a_4180_ = crate::leanh::lean_ctor_get(v___x_4163_, 0);
                    v_isSharedCheck_4193_ = (!crate::leanh::lean_is_exclusive(v___x_4163_)) as u8;
                    if v_isSharedCheck_4193_ == 0 {
                        v___x_4182_ = v___x_4163_;
                        v_isShared_4183_ = v_isSharedCheck_4193_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4180_);
                        crate::leanh::lean_dec(v___x_4163_);
                        v___x_4182_ = crate::leanh::lean_box(0);
                        v_isShared_4183_ = v_isSharedCheck_4193_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4171_ = crate::leanh::lean_box(0);
                v___x_4172_ = lean_io_promise_resolve(v___x_4171_, v_val_4146_);
                v___x_4173_ = l_IO_CancelToken_isSet(v_val_4157_);
                if v___x_4173_ == 0 {
                    if v_isShared_4170_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4169_, 0, v___x_4171_);
                        v___x_4175_ = v___x_4169_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4176_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4171_);
                        v___x_4175_ = v_reuseFailAlloc_4176_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4169_);
                    v___x_4177_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
                    return v___x_4177_;
                }
            }
            3 => {
                return v___x_4175_;
            }
            4 => {
                v___x_4184_ = lean_io_error_to_string(v_a_4180_);
                if v_isShared_4161_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4160_, 3);
                    crate::leanh::lean_ctor_set(v___x_4160_, 0, v___x_4184_);
                    v___x_4186_ = v___x_4160_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4192_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4184_);
                    v___x_4186_ = v_reuseFailAlloc_4192_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4187_ = l_Lean_MessageData_ofFormat(v___x_4186_);
                crate::leanh::lean_inc(v_ref_4156_);
                v___x_4188_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4188_, 0, v_ref_4156_);
                crate::leanh::lean_ctor_set(v___x_4188_, 1, v___x_4187_);
                if v_isShared_4183_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4182_, 0, v___x_4188_);
                    v___x_4190_ = v___x_4182_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
                    v___x_4190_ = v_reuseFailAlloc_4191_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4190_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed(
    mut v_val_4198_: *mut crate::leanh::LeanObject,
    mut v_x_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4207_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1(v_val_4198_, v_x_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
    crate::leanh::lean_dec(v___y_4205_);
    crate::leanh::lean_dec_ref(v___y_4204_);
    crate::leanh::lean_dec(v___y_4203_);
    crate::leanh::lean_dec_ref(v___y_4202_);
    crate::leanh::lean_dec(v___y_4201_);
    crate::leanh::lean_dec_ref(v___y_4200_);
    crate::leanh::lean_dec(v_val_4198_);
    return v_res_4207_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(
    mut v_x_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_a_4222_: *mut crate::leanh::LeanObject,
    mut v_a_4223_: *mut crate::leanh::LeanObject,
    mut v_a_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: u8 = 0;
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8410__overap_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4268_: u8 = 0;
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4226_ =
                    l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once__async___closed__1;
                v___x_4227_ = l_Lean_Syntax_isOfKind(v_x_4216_, v___x_4226_);
                if v___x_4227_ == 0 {
                    v___x_4228_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
                    return v___x_4228_;
                } else {
                    v___x_4229_ = lean_io_promise_new();
                    v___x_4230_ = l_Lean_Server_Test_Cancel_onceRef;
                    v___x_4231_ = lean_st_ref_take(v___x_4230_);
                    v___f_4232_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0;
                    crate::leanh::lean_inc(v___x_4229_);
                    v___f_4233_ = crate::leanh::lean_alloc_closure(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___lam__1___boxed as *mut core::ffi::c_void, 9, 1);
                    crate::leanh::lean_closure_set(v___f_4233_, 0, v___x_4229_);
                    if crate::leanh::lean_obj_tag(v___x_4231_) == 0 {
                        v___x_4273_ = l_IO_Promise_result_x21___redArg(v___x_4229_);
                        crate::leanh::lean_dec(v___x_4229_);
                        v___y_4235_ = v___x_4273_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4229_);
                        v_val_4274_ = crate::leanh::lean_ctor_get(v___x_4231_, 0);
                        crate::leanh::lean_inc(v_val_4274_);
                        v___y_4235_ = v_val_4274_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4236_, 0, v___y_4235_);
                v___x_4237_ = lean_st_ref_set(v___x_4230_, v___x_4236_);
                if crate::leanh::lean_obj_tag(v___x_4231_) == 1 {
                    crate::leanh::lean_dec_ref(v___f_4233_);
                    v_val_4238_ = crate::leanh::lean_ctor_get(v___x_4231_, 0);
                    v_isSharedCheck_4247_ = (!crate::leanh::lean_is_exclusive(v___x_4231_)) as u8;
                    if v_isSharedCheck_4247_ == 0 {
                        v___x_4240_ = v___x_4231_;
                        v_isShared_4241_ = v_isSharedCheck_4247_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4238_);
                        crate::leanh::lean_dec(v___x_4231_);
                        v___x_4240_ = crate::leanh::lean_box(0);
                        v_isShared_4241_ = v_isSharedCheck_4247_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4231_);
                    v___x_4248_ = l_IO_CancelToken_new();
                    v___x_4249_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4249_, 0, v___x_4248_);
                    v___x_4250_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__2;
                    v___x_4251_ = l_Lean_Name_toString(v___x_4250_, v___x_4227_);
                    crate::leanh::lean_inc_ref(v___x_4249_);
                    v___x_4252_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(
                        v___f_4233_,
                        v___x_4249_,
                        v___x_4251_,
                        v_a_4219_,
                        v_a_4220_,
                        v_a_4221_,
                        v_a_4222_,
                        v_a_4223_,
                        v_a_4224_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4252_) == 0 {
                        v_a_4253_ = crate::leanh::lean_ctor_get(v___x_4252_, 0);
                        crate::leanh::lean_inc(v_a_4253_);
                        crate::leanh::lean_dec_ref_known(v___x_4252_, 1);
                        v___x_4254_ = crate::leanh::lean_box(0);
                        v___x_4255_ = crate::leanh::lean_apply_1(v_a_4253_, v___x_4254_);
                        v___x_4256_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4257_ = lean_io_as_task(v___x_4255_, v___x_4256_);
                        v___x_4258_ = crate::leanh::lean_box(0);
                        v___x_4259_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1___closed__3);
                        v___x_4260_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4260_, 0, v___x_4258_);
                        crate::leanh::lean_ctor_set(v___x_4260_, 1, v___x_4259_);
                        crate::leanh::lean_ctor_set(v___x_4260_, 2, v___x_4249_);
                        crate::leanh::lean_ctor_set(v___x_4260_, 3, v___x_4257_);
                        v___x_4261_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4260_, v_a_4224_);
                        if crate::leanh::lean_obj_tag(v___x_4261_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4261_, 1);
                            v___x_4262_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0;
                            v___x_8410__overap_4263_ = lean_dbg_trace(v___x_4262_, v___f_4232_);
                            crate::leanh::lean_inc(v_a_4224_);
                            crate::leanh::lean_inc_ref(v_a_4223_);
                            crate::leanh::lean_inc(v_a_4222_);
                            crate::leanh::lean_inc_ref(v_a_4221_);
                            crate::leanh::lean_inc(v_a_4220_);
                            crate::leanh::lean_inc_ref(v_a_4219_);
                            crate::leanh::lean_inc(v_a_4218_);
                            crate::leanh::lean_inc_ref(v_a_4217_);
                            v___x_4264_ = crate::leanh::lean_apply_9(
                                v___x_8410__overap_4263_,
                                v_a_4217_,
                                v_a_4218_,
                                v_a_4219_,
                                v_a_4220_,
                                v_a_4221_,
                                v_a_4222_,
                                v_a_4223_,
                                v_a_4224_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_4264_;
                        } else {
                            return v___x_4261_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4249_, 1);
                        v_a_4265_ = crate::leanh::lean_ctor_get(v___x_4252_, 0);
                        v_isSharedCheck_4272_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4252_)) as u8;
                        if v_isSharedCheck_4272_ == 0 {
                            v___x_4267_ = v___x_4252_;
                            v_isShared_4268_ = v_isSharedCheck_4272_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4265_);
                            crate::leanh::lean_dec(v___x_4252_);
                            v___x_4267_ = crate::leanh::lean_box(0);
                            v_isShared_4268_ = v_isSharedCheck_4272_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4242_ = lean_io_wait(v_val_4238_);
                crate::leanh::lean_dec(v___x_4242_);
                v___x_4243_ = crate::leanh::lean_box(0);
                if v_isShared_4241_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4240_, 0);
                    crate::leanh::lean_ctor_set(v___x_4240_, 0, v___x_4243_);
                    v___x_4245_ = v___x_4240_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4243_);
                    v___x_4245_ = v_reuseFailAlloc_4246_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4245_;
            }
            4 => {
                if v_isShared_4268_ == 0 {
                    v___x_4270_ = v___x_4267_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
                    v___x_4270_ = v_reuseFailAlloc_4271_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___boxed(
    mut v_x_4275_: *mut crate::leanh::LeanObject,
    mut v_a_4276_: *mut crate::leanh::LeanObject,
    mut v_a_4277_: *mut crate::leanh::LeanObject,
    mut v_a_4278_: *mut crate::leanh::LeanObject,
    mut v_a_4279_: *mut crate::leanh::LeanObject,
    mut v_a_4280_: *mut crate::leanh::LeanObject,
    mut v_a_4281_: *mut crate::leanh::LeanObject,
    mut v_a_4282_: *mut crate::leanh::LeanObject,
    mut v_a_4283_: *mut crate::leanh::LeanObject,
    mut v_a_4284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4285_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1(v_x_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
    crate::leanh::lean_dec(v_a_4283_);
    crate::leanh::lean_dec_ref(v_a_4282_);
    crate::leanh::lean_dec(v_a_4281_);
    crate::leanh::lean_dec_ref(v_a_4280_);
    crate::leanh::lean_dec(v_a_4279_);
    crate::leanh::lean_dec_ref(v_a_4278_);
    crate::leanh::lean_dec(v_a_4277_);
    crate::leanh::lean_dec_ref(v_a_4276_);
    return v_res_4285_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(
    mut v_val_4286_: *mut crate::leanh::LeanObject,
    mut v_inst_4287_: *mut crate::leanh::LeanObject,
    mut v_a_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
    mut v___y_4290_: *mut crate::leanh::LeanObject,
    mut v___y_4291_: *mut crate::leanh::LeanObject,
    mut v___y_4292_: *mut crate::leanh::LeanObject,
    mut v___y_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4296_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_4286_);
    return v___x_4296_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___boxed(
    mut v_val_4297_: *mut crate::leanh::LeanObject,
    mut v_inst_4298_: *mut crate::leanh::LeanObject,
    mut v_a_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
    mut v___y_4303_: *mut crate::leanh::LeanObject,
    mut v___y_4304_: *mut crate::leanh::LeanObject,
    mut v___y_4305_: *mut crate::leanh::LeanObject,
    mut v___y_4306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4307_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0(v_val_4297_, v_inst_4298_, v_a_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
    crate::leanh::lean_dec(v___y_4305_);
    crate::leanh::lean_dec_ref(v___y_4304_);
    crate::leanh::lean_dec(v___y_4303_);
    crate::leanh::lean_dec_ref(v___y_4302_);
    crate::leanh::lean_dec(v___y_4301_);
    crate::leanh::lean_dec_ref(v___y_4300_);
    crate::leanh::lean_dec_ref(v_val_4297_);
    return v_res_4307_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(
    mut v_val_4324_: *mut crate::leanh::LeanObject,
    mut v_val_4325_: *mut crate::leanh::LeanObject,
    mut v_x_4326_: *mut crate::leanh::LeanObject,
    mut v___y_4327_: *mut crate::leanh::LeanObject,
    mut v___y_4328_: *mut crate::leanh::LeanObject,
    mut v___y_4329_: *mut crate::leanh::LeanObject,
    mut v___y_4330_: *mut crate::leanh::LeanObject,
    mut v___y_4331_: *mut crate::leanh::LeanObject,
    mut v___y_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4337_: u8 = 0;
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: u8 = 0;
    let mut v___x_4342_: u8 = 0;
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: u8 = 0;
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4359_: u8 = 0;
    let mut v_unused_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4364_: u8 = 0;
    let mut v_ref_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4375_: u8 = 0;
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut v_unused_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4334_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1_spec__0___redArg(v_val_4324_);
                if crate::leanh::lean_obj_tag(v___x_4334_) == 0 {
                    v_isSharedCheck_4376_ = (!crate::leanh::lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4376_ == 0 {
                        v_unused_4377_ = crate::leanh::lean_ctor_get(v___x_4334_, 0);
                        crate::leanh::lean_dec(v_unused_4377_);
                        v___x_4336_ = v___x_4334_;
                        v_isShared_4337_ = v_isSharedCheck_4376_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4334_);
                        v___x_4336_ = crate::leanh::lean_box(0);
                        v_isShared_4337_ = v_isSharedCheck_4376_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4334_;
                }
            }
            1 => {
                v___x_4338_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6;
                v___x_4339_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_4338_);
                if crate::leanh::lean_obj_tag(v___x_4339_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4339_, 1);
                    crate::leanh::lean_del_object(v___x_4336_);
                    v___x_4340_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
                    v___x_4341_ = 2;
                    v___x_4342_ = 0;
                    v___x_4343_ = l_Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__unblock__async__1_spec__1(v___x_4340_, v___x_4341_, v___x_4342_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
                    if crate::leanh::lean_obj_tag(v___x_4343_) == 0 {
                        v_isSharedCheck_4359_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4343_)) as u8;
                        if v_isSharedCheck_4359_ == 0 {
                            v_unused_4360_ = crate::leanh::lean_ctor_get(v___x_4343_, 0);
                            crate::leanh::lean_dec(v_unused_4360_);
                            v___x_4345_ = v___x_4343_;
                            v_isShared_4346_ = v_isSharedCheck_4359_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4343_);
                            v___x_4345_ = crate::leanh::lean_box(0);
                            v_isShared_4346_ = v_isSharedCheck_4359_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_4343_;
                    }
                } else {
                    v_a_4361_ = crate::leanh::lean_ctor_get(v___x_4339_, 0);
                    v_isSharedCheck_4375_ = (!crate::leanh::lean_is_exclusive(v___x_4339_)) as u8;
                    if v_isSharedCheck_4375_ == 0 {
                        v___x_4363_ = v___x_4339_;
                        v_isShared_4364_ = v_isSharedCheck_4375_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4361_);
                        crate::leanh::lean_dec(v___x_4339_);
                        v___x_4363_ = crate::leanh::lean_box(0);
                        v_isShared_4364_ = v_isSharedCheck_4375_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4347_ = crate::leanh::lean_box(0);
                v___x_4348_ = lean_io_promise_resolve(v___x_4347_, v_val_4325_);
                v_cancelTk_x3f_4349_ = crate::leanh::lean_ctor_get(v___y_4331_, 12);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_4349_) == 1 {
                    v_val_4350_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_4349_, 0);
                    v___x_4351_ = l_IO_CancelToken_isSet(v_val_4350_);
                    if v___x_4351_ == 0 {
                        if v_isShared_4346_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4345_, 0, v___x_4347_);
                            v___x_4353_ = v___x_4345_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4354_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4347_);
                            v___x_4353_ = v_reuseFailAlloc_4354_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4345_);
                        v___x_4355_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
                        return v___x_4355_;
                    }
                } else {
                    if v_isShared_4346_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4345_, 0, v___x_4347_);
                        v___x_4357_ = v___x_4345_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4347_);
                        v___x_4357_ = v_reuseFailAlloc_4358_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4353_;
            }
            4 => {
                return v___x_4357_;
            }
            5 => {
                v_ref_4365_ = crate::leanh::lean_ctor_get(v___y_4331_, 5);
                v___x_4366_ = lean_io_error_to_string(v_a_4361_);
                if v_isShared_4337_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4336_, 3);
                    crate::leanh::lean_ctor_set(v___x_4336_, 0, v___x_4366_);
                    v___x_4368_ = v___x_4336_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4374_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4366_);
                    v___x_4368_ = v_reuseFailAlloc_4374_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4369_ = l_Lean_MessageData_ofFormat(v___x_4368_);
                crate::leanh::lean_inc(v_ref_4365_);
                v___x_4370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4370_, 0, v_ref_4365_);
                crate::leanh::lean_ctor_set(v___x_4370_, 1, v___x_4369_);
                if v_isShared_4364_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4363_, 0, v___x_4370_);
                    v___x_4372_ = v___x_4363_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4373_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4370_);
                    v___x_4372_ = v_reuseFailAlloc_4373_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed(
    mut v_val_4378_: *mut crate::leanh::LeanObject,
    mut v_val_4379_: *mut crate::leanh::LeanObject,
    mut v_x_4380_: *mut crate::leanh::LeanObject,
    mut v___y_4381_: *mut crate::leanh::LeanObject,
    mut v___y_4382_: *mut crate::leanh::LeanObject,
    mut v___y_4383_: *mut crate::leanh::LeanObject,
    mut v___y_4384_: *mut crate::leanh::LeanObject,
    mut v___y_4385_: *mut crate::leanh::LeanObject,
    mut v___y_4386_: *mut crate::leanh::LeanObject,
    mut v___y_4387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4388_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1(v_val_4378_, v_val_4379_, v_x_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
    crate::leanh::lean_dec(v___y_4386_);
    crate::leanh::lean_dec_ref(v___y_4385_);
    crate::leanh::lean_dec(v___y_4384_);
    crate::leanh::lean_dec_ref(v___y_4383_);
    crate::leanh::lean_dec(v___y_4382_);
    crate::leanh::lean_dec_ref(v___y_4381_);
    crate::leanh::lean_dec(v_val_4379_);
    crate::leanh::lean_dec_ref(v_val_4378_);
    return v_res_4388_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4396_ = crate::leanh::lean_box(0);
    v___x_4397_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_4396_);
    return v___x_4397_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4399_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
    v___x_4400_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_4401_ = crate::leanh::lean_unsigned_to_nat(177);
    v___x_4402_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__3;
    v___x_4403_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10;
    v___x_4404_ = l_mkPanicMessageWithDecl(
        v___x_4403_,
        v___x_4402_,
        v___x_4401_,
        v___x_4400_,
        v___x_4399_,
    );
    return v___x_4404_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(
    mut v_x_4405_: *mut crate::leanh::LeanObject,
    mut v_a_4406_: *mut crate::leanh::LeanObject,
    mut v_a_4407_: *mut crate::leanh::LeanObject,
    mut v_a_4408_: *mut crate::leanh::LeanObject,
    mut v_a_4409_: *mut crate::leanh::LeanObject,
    mut v_a_4410_: *mut crate::leanh::LeanObject,
    mut v_a_4411_: *mut crate::leanh::LeanObject,
    mut v_a_4412_: *mut crate::leanh::LeanObject,
    mut v_a_4413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: u8 = 0;
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4429_: u8 = 0;
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut v_cancelTk_x3f_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8376__overap_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4457_: u8 = 0;
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4461_: u8 = 0;
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4415_ = l_Lean_Server_Test_Cancel_tacticWait__for__main__cancel__once__async___closed__1;
                v___x_4416_ = l_Lean_Syntax_isOfKind(v_x_4405_, v___x_4415_);
                if v___x_4416_ == 0 {
                    v___x_4417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
                    return v___x_4417_;
                } else {
                    v___x_4418_ = lean_io_promise_new();
                    v___x_4419_ = l_Lean_Server_Test_Cancel_onceRef;
                    v___x_4420_ = lean_st_ref_take(v___x_4419_);
                    v___f_4421_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__async__1___closed__0;
                    if crate::leanh::lean_obj_tag(v___x_4420_) == 0 {
                        v___x_4464_ = l_IO_Promise_result_x21___redArg(v___x_4418_);
                        v___y_4423_ = v___x_4464_;
                        state = 1;
                        continue;
                    } else {
                        v_val_4465_ = crate::leanh::lean_ctor_get(v___x_4420_, 0);
                        crate::leanh::lean_inc(v_val_4465_);
                        v___y_4423_ = v_val_4465_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4424_, 0, v___y_4423_);
                v___x_4425_ = lean_st_ref_set(v___x_4419_, v___x_4424_);
                if crate::leanh::lean_obj_tag(v___x_4420_) == 1 {
                    crate::leanh::lean_dec(v___x_4418_);
                    v_val_4426_ = crate::leanh::lean_ctor_get(v___x_4420_, 0);
                    v_isSharedCheck_4435_ = (!crate::leanh::lean_is_exclusive(v___x_4420_)) as u8;
                    if v_isSharedCheck_4435_ == 0 {
                        v___x_4428_ = v___x_4420_;
                        v_isShared_4429_ = v_isSharedCheck_4435_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4426_);
                        crate::leanh::lean_dec(v___x_4420_);
                        v___x_4428_ = crate::leanh::lean_box(0);
                        v_isShared_4429_ = v_isSharedCheck_4435_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4420_);
                    v_cancelTk_x3f_4436_ = crate::leanh::lean_ctor_get(v_a_4412_, 12);
                    if crate::leanh::lean_obj_tag(v_cancelTk_x3f_4436_) == 1 {
                        v_val_4437_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_4436_, 0);
                        crate::leanh::lean_inc(v_val_4437_);
                        v___f_4438_ = crate::leanh::lean_alloc_closure(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___lam__1___boxed as *mut core::ffi::c_void, 10, 2);
                        crate::leanh::lean_closure_set(v___f_4438_, 0, v_val_4437_);
                        crate::leanh::lean_closure_set(v___f_4438_, 1, v___x_4418_);
                        v___x_4439_ = crate::leanh::lean_box(0);
                        v___x_4440_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__1;
                        v___x_4441_ = l_Lean_Name_toString(v___x_4440_, v___x_4416_);
                        v___x_4442_ = l_Lean_Elab_Term_wrapAsyncAsSnapshot___redArg(
                            v___f_4438_,
                            v___x_4439_,
                            v___x_4441_,
                            v_a_4408_,
                            v_a_4409_,
                            v_a_4410_,
                            v_a_4411_,
                            v_a_4412_,
                            v_a_4413_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4442_) == 0 {
                            v_a_4443_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
                            crate::leanh::lean_inc(v_a_4443_);
                            crate::leanh::lean_dec_ref_known(v___x_4442_, 1);
                            v___x_4444_ = crate::leanh::lean_box(0);
                            v___x_4445_ = crate::leanh::lean_apply_1(v_a_4443_, v___x_4444_);
                            v___x_4446_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4447_ = lean_io_as_task(v___x_4445_, v___x_4446_);
                            v___x_4448_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
                            crate::leanh::lean_inc_ref(v_cancelTk_x3f_4436_);
                            v___x_4449_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4449_, 0, v___x_4439_);
                            crate::leanh::lean_ctor_set(v___x_4449_, 1, v___x_4448_);
                            crate::leanh::lean_ctor_set(v___x_4449_, 2, v_cancelTk_x3f_4436_);
                            crate::leanh::lean_ctor_set(v___x_4449_, 3, v___x_4447_);
                            v___x_4450_ =
                                l_Lean_Core_logSnapshotTask___redArg(v___x_4449_, v_a_4413_);
                            if crate::leanh::lean_obj_tag(v___x_4450_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4450_, 1);
                                v___x_4451_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___closed__0;
                                v___x_8376__overap_4452_ = lean_dbg_trace(v___x_4451_, v___f_4421_);
                                crate::leanh::lean_inc(v_a_4413_);
                                crate::leanh::lean_inc_ref(v_a_4412_);
                                crate::leanh::lean_inc(v_a_4411_);
                                crate::leanh::lean_inc_ref(v_a_4410_);
                                crate::leanh::lean_inc(v_a_4409_);
                                crate::leanh::lean_inc_ref(v_a_4408_);
                                crate::leanh::lean_inc(v_a_4407_);
                                crate::leanh::lean_inc_ref(v_a_4406_);
                                v___x_4453_ = crate::leanh::lean_apply_9(
                                    v___x_8376__overap_4452_,
                                    v_a_4406_,
                                    v_a_4407_,
                                    v_a_4408_,
                                    v_a_4409_,
                                    v_a_4410_,
                                    v_a_4411_,
                                    v_a_4412_,
                                    v_a_4413_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_4453_;
                            } else {
                                return v___x_4450_;
                            }
                        } else {
                            v_a_4454_ = crate::leanh::lean_ctor_get(v___x_4442_, 0);
                            v_isSharedCheck_4461_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4442_)) as u8;
                            if v_isSharedCheck_4461_ == 0 {
                                v___x_4456_ = v___x_4442_;
                                v_isShared_4457_ = v_isSharedCheck_4461_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4454_);
                                crate::leanh::lean_dec(v___x_4442_);
                                v___x_4456_ = crate::leanh::lean_box(0);
                                v_isShared_4457_ = v_isSharedCheck_4461_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4418_);
                        v___x_4462_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__4);
                        v___x_4463_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_4462_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
                        return v___x_4463_;
                    }
                }
            }
            2 => {
                v___x_4430_ = lean_io_wait(v_val_4426_);
                crate::leanh::lean_dec(v___x_4430_);
                v___x_4431_ = crate::leanh::lean_box(0);
                if v_isShared_4429_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4428_, 0);
                    crate::leanh::lean_ctor_set(v___x_4428_, 0, v___x_4431_);
                    v___x_4433_ = v___x_4428_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4434_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4431_);
                    v___x_4433_ = v_reuseFailAlloc_4434_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4433_;
            }
            4 => {
                if v_isShared_4457_ == 0 {
                    v___x_4459_ = v___x_4456_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
                    v___x_4459_ = v_reuseFailAlloc_4460_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4459_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___boxed(
    mut v_x_4466_: *mut crate::leanh::LeanObject,
    mut v_a_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
    mut v_a_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
    mut v_a_4472_: *mut crate::leanh::LeanObject,
    mut v_a_4473_: *mut crate::leanh::LeanObject,
    mut v_a_4474_: *mut crate::leanh::LeanObject,
    mut v_a_4475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1(v_x_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_);
    crate::leanh::lean_dec(v_a_4474_);
    crate::leanh::lean_dec_ref(v_a_4473_);
    crate::leanh::lean_dec(v_a_4472_);
    crate::leanh::lean_dec_ref(v_a_4471_);
    crate::leanh::lean_dec(v_a_4470_);
    crate::leanh::lean_dec_ref(v_a_4469_);
    crate::leanh::lean_dec(v_a_4468_);
    crate::leanh::lean_dec_ref(v_a_4467_);
    return v_res_4476_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4478_ = crate::leanh::lean_box(0);
    v___x_4479_ = lean_st_mk_ref(v___x_4478_);
    v___x_4480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4480_, 0, v___x_4479_);
    return v___x_4480_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2____boxed(
    mut v_a_4481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4482_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
    return v_res_4482_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4511_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg___closed__0);
    v___x_4512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4512_, 0, v___x_4511_);
    return v___x_4512_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg___boxed(
    mut v___y_4513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
    return v_res_4514_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(
    mut v_00_u03b1_4515_: *mut crate::leanh::LeanObject,
    mut v___y_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4519_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
    return v___x_4519_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___boxed(
    mut v_00_u03b1_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
    mut v___y_4522_: *mut crate::leanh::LeanObject,
    mut v___y_4523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4524_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0(v_00_u03b1_4520_, v___y_4521_, v___y_4522_);
    crate::leanh::lean_dec(v___y_4522_);
    crate::leanh::lean_dec_ref(v___y_4521_);
    return v_res_4524_;
}
pub unsafe fn l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(
    mut v_msg_4526_: *mut crate::leanh::LeanObject,
    mut v___y_4527_: *mut crate::leanh::LeanObject,
    mut v___y_4528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553__overap_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4530_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___closed__0;
    v___x_4553__overap_4531_ = lean_panic_fn_borrowed(v___f_4530_, v_msg_4526_);
    crate::leanh::lean_inc(v___y_4528_);
    crate::leanh::lean_inc_ref(v___y_4527_);
    v___x_4532_ = crate::leanh::lean_apply_3(
        v___x_4553__overap_4531_,
        v___y_4527_,
        v___y_4528_,
        crate::leanh::lean_box(0),
    );
    return v___x_4532_;
}
pub unsafe fn l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3___boxed(
    mut v_msg_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4537_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v_msg_4533_, v___y_4534_, v___y_4535_);
    crate::leanh::lean_dec(v___y_4535_);
    crate::leanh::lean_dec_ref(v___y_4534_);
    return v_res_4537_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4538_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4538_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4539_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__0);
    v___x_4540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4540_, 0, v___x_4539_);
    return v___x_4540_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4541_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
    v___x_4542_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4543_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4543_, 0, v___x_4542_);
    crate::leanh::lean_ctor_set(v___x_4543_, 1, v___x_4542_);
    crate::leanh::lean_ctor_set(v___x_4543_, 2, v___x_4542_);
    crate::leanh::lean_ctor_set(v___x_4543_, 3, v___x_4542_);
    crate::leanh::lean_ctor_set(v___x_4543_, 4, v___x_4541_);
    crate::leanh::lean_ctor_set(v___x_4543_, 5, v___x_4541_);
    crate::leanh::lean_ctor_set(v___x_4543_, 6, v___x_4541_);
    crate::leanh::lean_ctor_set(v___x_4543_, 7, v___x_4541_);
    crate::leanh::lean_ctor_set(v___x_4543_, 8, v___x_4541_);
    crate::leanh::lean_ctor_set(v___x_4543_, 9, v___x_4541_);
    return v___x_4543_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4544_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4545_ = lean_mk_empty_array_with_capacity(v___x_4544_);
    v___x_4546_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4546_, 0, v___x_4545_);
    return v___x_4546_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4547_: usize = 0;
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4547_ = 5usize;
    v___x_4548_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4549_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4550_ = lean_mk_empty_array_with_capacity(v___x_4549_);
    v___x_4551_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__3);
    v___x_4552_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4552_, 0, v___x_4551_);
    crate::leanh::lean_ctor_set(v___x_4552_, 1, v___x_4550_);
    crate::leanh::lean_ctor_set(v___x_4552_, 2, v___x_4548_);
    crate::leanh::lean_ctor_set(v___x_4552_, 3, v___x_4548_);
    crate::leanh::lean_ctor_set_usize(v___x_4552_, 4, v___x_4547_);
    return v___x_4552_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ = crate::leanh::lean_box(1);
    v___x_4554_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__4);
    v___x_4555_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__1);
    v___x_4556_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4556_, 0, v___x_4555_);
    crate::leanh::lean_ctor_set(v___x_4556_, 1, v___x_4554_);
    crate::leanh::lean_ctor_set(v___x_4556_, 2, v___x_4553_);
    return v___x_4556_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(
    mut v_msgData_4557_: *mut crate::leanh::LeanObject,
    mut v___y_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4561_ = lean_st_ref_get(v___y_4559_);
    v_env_4562_ = crate::leanh::lean_ctor_get(v___x_4561_, 0);
    crate::leanh::lean_inc_ref(v_env_4562_);
    crate::leanh::lean_dec(v___x_4561_);
    v_options_4563_ = crate::leanh::lean_ctor_get(v___y_4558_, 2);
    v___x_4564_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__2);
    v___x_4565_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___closed__5);
    crate::leanh::lean_inc_ref(v_options_4563_);
    v___x_4566_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4566_, 0, v_env_4562_);
    crate::leanh::lean_ctor_set(v___x_4566_, 1, v___x_4564_);
    crate::leanh::lean_ctor_set(v___x_4566_, 2, v___x_4565_);
    crate::leanh::lean_ctor_set(v___x_4566_, 3, v_options_4563_);
    v___x_4567_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4567_, 0, v___x_4566_);
    crate::leanh::lean_ctor_set(v___x_4567_, 1, v_msgData_4557_);
    v___x_4568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4568_, 0, v___x_4567_);
    return v___x_4568_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5___boxed(
    mut v_msgData_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4573_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v_msgData_4569_, v___y_4570_, v___y_4571_);
    crate::leanh::lean_dec(v___y_4571_);
    crate::leanh::lean_dec_ref(v___y_4570_);
    return v_res_4573_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(
    mut v_ref_4574_: *mut crate::leanh::LeanObject,
    mut v_msgData_4575_: *mut crate::leanh::LeanObject,
    mut v_severity_4576_: u8,
    mut v_isSilent_4577_: u8,
    mut v___y_4578_: *mut crate::leanh::LeanObject,
    mut v___y_4579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4583_: u8 = 0;
    let mut v___y_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4585_: u8 = 0;
    let mut v___y_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4605_: u8 = 0;
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4616_: u8 = 0;
    let mut v___y_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4619_: u8 = 0;
    let mut v___y_4620_: u8 = 0;
    let mut v___y_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4622_: u8 = 0;
    let mut v___y_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4641_: u8 = 0;
    let mut v___y_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4644_: u8 = 0;
    let mut v___y_4645_: u8 = 0;
    let mut v___y_4646_: u8 = 0;
    let mut v___y_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4655_: u8 = 0;
    let mut v___y_4656_: u8 = 0;
    let mut v___y_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4660_: u8 = 0;
    let mut v_ref_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: u8 = 0;
    let mut v___y_4667_: u8 = 0;
    let mut v___y_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4672_: u8 = 0;
    let mut v___y_4673_: u8 = 0;
    let mut v___y_4675_: u8 = 0;
    let mut v_fileName_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4680_: u8 = 0;
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u8 = 0;
    let mut v___x_4685_: u8 = 0;
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: u8 = 0;
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4665_ = 2;
                v___x_4690_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4576_, v___x_4665_);
                if v___x_4690_ == 0 {
                    v___y_4675_ = v___x_4690_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_4575_);
                    v___x_4691_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4575_);
                    v___y_4675_ = v___x_4691_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4591_ = lean_st_ref_take(v___y_4590_);
                v_currNamespace_4592_ = crate::leanh::lean_ctor_get(v___y_4589_, 6);
                v_openDecls_4593_ = crate::leanh::lean_ctor_get(v___y_4589_, 7);
                v_env_4594_ = crate::leanh::lean_ctor_get(v___x_4591_, 0);
                v_nextMacroScope_4595_ = crate::leanh::lean_ctor_get(v___x_4591_, 1);
                v_ngen_4596_ = crate::leanh::lean_ctor_get(v___x_4591_, 2);
                v_auxDeclNGen_4597_ = crate::leanh::lean_ctor_get(v___x_4591_, 3);
                v_traceState_4598_ = crate::leanh::lean_ctor_get(v___x_4591_, 4);
                v_cache_4599_ = crate::leanh::lean_ctor_get(v___x_4591_, 5);
                v_messages_4600_ = crate::leanh::lean_ctor_get(v___x_4591_, 6);
                v_infoState_4601_ = crate::leanh::lean_ctor_get(v___x_4591_, 7);
                v_snapshotTasks_4602_ = crate::leanh::lean_ctor_get(v___x_4591_, 8);
                v_isSharedCheck_4616_ = (!crate::leanh::lean_is_exclusive(v___x_4591_)) as u8;
                if v_isSharedCheck_4616_ == 0 {
                    v___x_4604_ = v___x_4591_;
                    v_isShared_4605_ = v_isSharedCheck_4616_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4602_);
                    crate::leanh::lean_inc(v_infoState_4601_);
                    crate::leanh::lean_inc(v_messages_4600_);
                    crate::leanh::lean_inc(v_cache_4599_);
                    crate::leanh::lean_inc(v_traceState_4598_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4597_);
                    crate::leanh::lean_inc(v_ngen_4596_);
                    crate::leanh::lean_inc(v_nextMacroScope_4595_);
                    crate::leanh::lean_inc(v_env_4594_);
                    crate::leanh::lean_dec(v___x_4591_);
                    v___x_4604_ = crate::leanh::lean_box(0);
                    v_isShared_4605_ = v_isSharedCheck_4616_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_4593_);
                crate::leanh::lean_inc(v_currNamespace_4592_);
                v___x_4606_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4606_, 0, v_currNamespace_4592_);
                crate::leanh::lean_ctor_set(v___x_4606_, 1, v_openDecls_4593_);
                v___x_4607_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4607_, 0, v___x_4606_);
                crate::leanh::lean_ctor_set(v___x_4607_, 1, v___y_4584_);
                crate::leanh::lean_inc_ref(v___y_4588_);
                crate::leanh::lean_inc_ref(v___y_4587_);
                v___x_4608_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_4608_, 0, v___y_4587_);
                crate::leanh::lean_ctor_set(v___x_4608_, 1, v___y_4582_);
                crate::leanh::lean_ctor_set(v___x_4608_, 2, v___y_4586_);
                crate::leanh::lean_ctor_set(v___x_4608_, 3, v___y_4588_);
                crate::leanh::lean_ctor_set(v___x_4608_, 4, v___x_4607_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4608_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_4585_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4608_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_4583_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4608_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4577_,
                );
                v___x_4609_ = l_Lean_MessageLog_add(v___x_4608_, v_messages_4600_);
                if v_isShared_4605_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4604_, 6, v___x_4609_);
                    v___x_4611_ = v___x_4604_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4615_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_env_4594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 1, v_nextMacroScope_4595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 2, v_ngen_4596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 3, v_auxDeclNGen_4597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 4, v_traceState_4598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 5, v_cache_4599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 6, v___x_4609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 7, v_infoState_4601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 8, v_snapshotTasks_4602_);
                    v___x_4611_ = v_reuseFailAlloc_4615_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4612_ = lean_st_ref_set(v___y_4590_, v___x_4611_);
                v___x_4613_ = crate::leanh::lean_box(0);
                v___x_4614_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4614_, 0, v___x_4613_);
                return v___x_4614_;
            }
            4 => {
                v___x_4626_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4575_,
                    );
                v___x_4627_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4_spec__5(v___x_4626_, v___y_4578_, v___y_4579_);
                v_a_4628_ = crate::leanh::lean_ctor_get(v___x_4627_, 0);
                v_isSharedCheck_4641_ = (!crate::leanh::lean_is_exclusive(v___x_4627_)) as u8;
                if v_isSharedCheck_4641_ == 0 {
                    v___x_4630_ = v___x_4627_;
                    v_isShared_4631_ = v_isSharedCheck_4641_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4628_);
                    crate::leanh::lean_dec(v___x_4627_);
                    v___x_4630_ = crate::leanh::lean_box(0);
                    v_isShared_4631_ = v_isSharedCheck_4641_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_4624_, 2);
                v___x_4632_ = l_Lean_FileMap_toPosition(v___y_4624_, v___y_4621_);
                crate::leanh::lean_dec(v___y_4621_);
                v___x_4633_ = l_Lean_FileMap_toPosition(v___y_4624_, v___y_4625_);
                crate::leanh::lean_dec(v___y_4625_);
                v___x_4634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4634_, 0, v___x_4633_);
                v___x_4635_ = l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___closed__0;
                if v___y_4622_ == 0 {
                    crate::leanh::lean_del_object(v___x_4630_);
                    crate::leanh::lean_dec_ref(v___y_4618_);
                    v___y_4582_ = v___x_4632_;
                    v___y_4583_ = v___y_4619_;
                    v___y_4584_ = v_a_4628_;
                    v___y_4585_ = v___y_4620_;
                    v___y_4586_ = v___x_4634_;
                    v___y_4587_ = v___y_4623_;
                    v___y_4588_ = v___x_4635_;
                    v___y_4589_ = v___y_4578_;
                    v___y_4590_ = v___y_4579_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4628_);
                    v___x_4636_ = l_Lean_MessageData_hasTag(v___y_4618_, v_a_4628_);
                    if v___x_4636_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4634_, 1);
                        crate::leanh::lean_dec_ref(v___x_4632_);
                        crate::leanh::lean_dec(v_a_4628_);
                        v___x_4637_ = crate::leanh::lean_box(0);
                        if v_isShared_4631_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4630_, 0, v___x_4637_);
                            v___x_4639_ = v___x_4630_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4640_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4637_);
                            v___x_4639_ = v_reuseFailAlloc_4640_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4630_);
                        v___y_4582_ = v___x_4632_;
                        v___y_4583_ = v___y_4619_;
                        v___y_4584_ = v_a_4628_;
                        v___y_4585_ = v___y_4620_;
                        v___y_4586_ = v___x_4634_;
                        v___y_4587_ = v___y_4623_;
                        v___y_4588_ = v___x_4635_;
                        v___y_4589_ = v___y_4578_;
                        v___y_4590_ = v___y_4579_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4639_;
            }
            7 => {
                v___x_4651_ = l_Lean_Syntax_getTailPos_x3f(v___y_4649_, v___y_4645_);
                crate::leanh::lean_dec(v___y_4649_);
                if crate::leanh::lean_obj_tag(v___x_4651_) == 0 {
                    crate::leanh::lean_inc(v___y_4650_);
                    v___y_4618_ = v___y_4643_;
                    v___y_4619_ = v___y_4644_;
                    v___y_4620_ = v___y_4645_;
                    v___y_4621_ = v___y_4650_;
                    v___y_4622_ = v___y_4646_;
                    v___y_4623_ = v___y_4647_;
                    v___y_4624_ = v___y_4648_;
                    v___y_4625_ = v___y_4650_;
                    state = 4;
                    continue;
                } else {
                    v_val_4652_ = crate::leanh::lean_ctor_get(v___x_4651_, 0);
                    crate::leanh::lean_inc(v_val_4652_);
                    crate::leanh::lean_dec_ref_known(v___x_4651_, 1);
                    v___y_4618_ = v___y_4643_;
                    v___y_4619_ = v___y_4644_;
                    v___y_4620_ = v___y_4645_;
                    v___y_4621_ = v___y_4650_;
                    v___y_4622_ = v___y_4646_;
                    v___y_4623_ = v___y_4647_;
                    v___y_4624_ = v___y_4648_;
                    v___y_4625_ = v_val_4652_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4661_ = l_Lean_replaceRef(v_ref_4574_, v___y_4658_);
                v___x_4662_ = l_Lean_Syntax_getPos_x3f(v_ref_4661_, v___y_4655_);
                if crate::leanh::lean_obj_tag(v___x_4662_) == 0 {
                    v___x_4663_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4643_ = v___y_4654_;
                    v___y_4644_ = v___y_4660_;
                    v___y_4645_ = v___y_4655_;
                    v___y_4646_ = v___y_4656_;
                    v___y_4647_ = v___y_4657_;
                    v___y_4648_ = v___y_4659_;
                    v___y_4649_ = v_ref_4661_;
                    v___y_4650_ = v___x_4663_;
                    state = 7;
                    continue;
                } else {
                    v_val_4664_ = crate::leanh::lean_ctor_get(v___x_4662_, 0);
                    crate::leanh::lean_inc(v_val_4664_);
                    crate::leanh::lean_dec_ref_known(v___x_4662_, 1);
                    v___y_4643_ = v___y_4654_;
                    v___y_4644_ = v___y_4660_;
                    v___y_4645_ = v___y_4655_;
                    v___y_4646_ = v___y_4656_;
                    v___y_4647_ = v___y_4657_;
                    v___y_4648_ = v___y_4659_;
                    v___y_4649_ = v_ref_4661_;
                    v___y_4650_ = v_val_4664_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4673_ == 0 {
                    v___y_4654_ = v___y_4669_;
                    v___y_4655_ = v___y_4672_;
                    v___y_4656_ = v___y_4667_;
                    v___y_4657_ = v___y_4668_;
                    v___y_4658_ = v___y_4670_;
                    v___y_4659_ = v___y_4671_;
                    v___y_4660_ = v_severity_4576_;
                    state = 8;
                    continue;
                } else {
                    v___y_4654_ = v___y_4669_;
                    v___y_4655_ = v___y_4672_;
                    v___y_4656_ = v___y_4667_;
                    v___y_4657_ = v___y_4668_;
                    v___y_4658_ = v___y_4670_;
                    v___y_4659_ = v___y_4671_;
                    v___y_4660_ = v___x_4665_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4675_ == 0 {
                    v_fileName_4676_ = crate::leanh::lean_ctor_get(v___y_4578_, 0);
                    v_fileMap_4677_ = crate::leanh::lean_ctor_get(v___y_4578_, 1);
                    v_options_4678_ = crate::leanh::lean_ctor_get(v___y_4578_, 2);
                    v_ref_4679_ = crate::leanh::lean_ctor_get(v___y_4578_, 5);
                    v_suppressElabErrors_4680_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4578_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4681_ = crate::leanh::lean_box((v___y_4675_) as usize);
                    v___x_4682_ = crate::leanh::lean_box((v_suppressElabErrors_4680_) as usize);
                    v___f_4683_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_4683_, 0, v___x_4681_);
                    crate::leanh::lean_closure_set(v___f_4683_, 1, v___x_4682_);
                    v___x_4684_ = 1;
                    v___x_4685_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4576_, v___x_4684_);
                    if v___x_4685_ == 0 {
                        v___y_4667_ = v_suppressElabErrors_4680_;
                        v___y_4668_ = v_fileName_4676_;
                        v___y_4669_ = v___f_4683_;
                        v___y_4670_ = v_ref_4679_;
                        v___y_4671_ = v_fileMap_4677_;
                        v___y_4672_ = v___y_4675_;
                        v___y_4673_ = v___x_4685_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4686_ = l_Lean_warningAsError;
                        v___x_4687_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__1_spec__1_spec__5(v_options_4678_, v___x_4686_);
                        v___y_4667_ = v_suppressElabErrors_4680_;
                        v___y_4668_ = v_fileName_4676_;
                        v___y_4669_ = v___f_4683_;
                        v___y_4670_ = v_ref_4679_;
                        v___y_4671_ = v_fileMap_4677_;
                        v___y_4672_ = v___y_4675_;
                        v___y_4673_ = v___x_4687_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_4575_);
                    v___x_4688_ = crate::leanh::lean_box(0);
                    v___x_4689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4689_, 0, v___x_4688_);
                    return v___x_4689_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4___boxed(
    mut v_ref_4692_: *mut crate::leanh::LeanObject,
    mut v_msgData_4693_: *mut crate::leanh::LeanObject,
    mut v_severity_4694_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4695_: *mut crate::leanh::LeanObject,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4699_: u8 = 0;
    let mut v_isSilent_boxed_4700_: u8 = 0;
    let mut v_res_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4699_ = (crate::leanh::lean_unbox(v_severity_4694_) as u8);
    v_isSilent_boxed_4700_ = (crate::leanh::lean_unbox(v_isSilent_4695_) as u8);
    v_res_4701_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_4692_, v_msgData_4693_, v_severity_boxed_4699_, v_isSilent_boxed_4700_, v___y_4696_, v___y_4697_);
    crate::leanh::lean_dec(v___y_4697_);
    crate::leanh::lean_dec_ref(v___y_4696_);
    crate::leanh::lean_dec(v_ref_4692_);
    return v_res_4701_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(
    mut v_msgData_4702_: *mut crate::leanh::LeanObject,
    mut v_severity_4703_: u8,
    mut v_isSilent_4704_: u8,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4708_ = crate::leanh::lean_ctor_get(v___y_4705_, 5);
    v___x_4709_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2_spec__4(v_ref_4708_, v_msgData_4702_, v_severity_4703_, v_isSilent_4704_, v___y_4705_, v___y_4706_);
    return v___x_4709_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2___boxed(
    mut v_msgData_4710_: *mut crate::leanh::LeanObject,
    mut v_severity_4711_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4712_: *mut crate::leanh::LeanObject,
    mut v___y_4713_: *mut crate::leanh::LeanObject,
    mut v___y_4714_: *mut crate::leanh::LeanObject,
    mut v___y_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4716_: u8 = 0;
    let mut v_isSilent_boxed_4717_: u8 = 0;
    let mut v_res_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4716_ = (crate::leanh::lean_unbox(v_severity_4711_) as u8);
    v_isSilent_boxed_4717_ = (crate::leanh::lean_unbox(v_isSilent_4712_) as u8);
    v_res_4718_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_4710_, v_severity_boxed_4716_, v_isSilent_boxed_4717_, v___y_4713_, v___y_4714_);
    crate::leanh::lean_dec(v___y_4714_);
    crate::leanh::lean_dec_ref(v___y_4713_);
    return v_res_4718_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(
    mut v_msgData_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4723_: u8 = 0;
    let mut v___x_4724_: u8 = 0;
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4723_ = 0;
    v___x_4724_ = 0;
    v___x_4725_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2_spec__2(v_msgData_4719_, v___x_4723_, v___x_4724_, v___y_4720_, v___y_4721_);
    return v___x_4725_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2___boxed(
    mut v_msgData_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4730_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v_msgData_4726_, v___y_4727_, v___y_4728_);
    crate::leanh::lean_dec(v___y_4728_);
    crate::leanh::lean_dec_ref(v___y_4727_);
    return v_res_4730_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(
    mut v_val_4731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4733_: u8 = 0;
    let mut v___x_4734_: u32 = 0;
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4733_ = l_IO_CancelToken_isSet(v_val_4731_);
                if v___x_4733_ == 0 {
                    v___x_4734_ = 30;
                    v___x_4735_ = l_IO_sleep(v___x_4734_);
                    state = 0;
                    continue;
                } else {
                    v___x_4737_ = crate::leanh::lean_box(0);
                    v___x_4738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4738_, 0, v___x_4737_);
                    return v___x_4738_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg___boxed(
    mut v_val_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4741_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_4739_);
    crate::leanh::lean_dec_ref(v_val_4739_);
    return v_res_4741_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(
    mut v_val_4742_: *mut crate::leanh::LeanObject,
    mut v_val_4743_: *mut crate::leanh::LeanObject,
    mut v_x_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
    mut v___y_4746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4751_: u8 = 0;
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4758_: u8 = 0;
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: u8 = 0;
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4771_: u8 = 0;
    let mut v_unused_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4776_: u8 = 0;
    let mut v_ref_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v_isSharedCheck_4788_: u8 = 0;
    let mut v_unused_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4748_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_4742_);
                if crate::leanh::lean_obj_tag(v___x_4748_) == 0 {
                    v_isSharedCheck_4788_ = (!crate::leanh::lean_is_exclusive(v___x_4748_)) as u8;
                    if v_isSharedCheck_4788_ == 0 {
                        v_unused_4789_ = crate::leanh::lean_ctor_get(v___x_4748_, 0);
                        crate::leanh::lean_dec(v_unused_4789_);
                        v___x_4750_ = v___x_4748_;
                        v_isShared_4751_ = v_isSharedCheck_4788_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4748_);
                        v___x_4750_ = crate::leanh::lean_box(0);
                        v_isShared_4751_ = v_isSharedCheck_4788_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4748_;
                }
            }
            1 => {
                v___x_4752_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__6;
                v___x_4753_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_4752_);
                if crate::leanh::lean_obj_tag(v___x_4753_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4753_, 1);
                    crate::leanh::lean_del_object(v___x_4750_);
                    v___x_4754_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__9);
                    v___x_4755_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_4754_, v___y_4745_, v___y_4746_);
                    if crate::leanh::lean_obj_tag(v___x_4755_) == 0 {
                        v_isSharedCheck_4771_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4755_)) as u8;
                        if v_isSharedCheck_4771_ == 0 {
                            v_unused_4772_ = crate::leanh::lean_ctor_get(v___x_4755_, 0);
                            crate::leanh::lean_dec(v_unused_4772_);
                            v___x_4757_ = v___x_4755_;
                            v_isShared_4758_ = v_isSharedCheck_4771_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4755_);
                            v___x_4757_ = crate::leanh::lean_box(0);
                            v_isShared_4758_ = v_isSharedCheck_4771_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_4755_;
                    }
                } else {
                    v_a_4773_ = crate::leanh::lean_ctor_get(v___x_4753_, 0);
                    v_isSharedCheck_4787_ = (!crate::leanh::lean_is_exclusive(v___x_4753_)) as u8;
                    if v_isSharedCheck_4787_ == 0 {
                        v___x_4775_ = v___x_4753_;
                        v_isShared_4776_ = v_isSharedCheck_4787_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4773_);
                        crate::leanh::lean_dec(v___x_4753_);
                        v___x_4775_ = crate::leanh::lean_box(0);
                        v_isShared_4776_ = v_isSharedCheck_4787_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4759_ = crate::leanh::lean_box(0);
                v___x_4760_ = lean_io_promise_resolve(v___x_4759_, v_val_4743_);
                v_cancelTk_x3f_4761_ = crate::leanh::lean_ctor_get(v___y_4745_, 12);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_4761_) == 1 {
                    v_val_4762_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_4761_, 0);
                    v___x_4763_ = l_IO_CancelToken_isSet(v_val_4762_);
                    if v___x_4763_ == 0 {
                        if v_isShared_4758_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4757_, 0, v___x_4759_);
                            v___x_4765_ = v___x_4757_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4766_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4766_, 0, v___x_4759_);
                            v___x_4765_ = v_reuseFailAlloc_4766_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4757_);
                        v___x_4767_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
                        return v___x_4767_;
                    }
                } else {
                    if v_isShared_4758_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4757_, 0, v___x_4759_);
                        v___x_4769_ = v___x_4757_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4759_);
                        v___x_4769_ = v_reuseFailAlloc_4770_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4765_;
            }
            4 => {
                return v___x_4769_;
            }
            5 => {
                v_ref_4777_ = crate::leanh::lean_ctor_get(v___y_4745_, 5);
                v___x_4778_ = lean_io_error_to_string(v_a_4773_);
                if v_isShared_4751_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4750_, 3);
                    crate::leanh::lean_ctor_set(v___x_4750_, 0, v___x_4778_);
                    v___x_4780_ = v___x_4750_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4778_);
                    v___x_4780_ = v_reuseFailAlloc_4786_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4781_ = l_Lean_MessageData_ofFormat(v___x_4780_);
                crate::leanh::lean_inc(v_ref_4777_);
                v___x_4782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4782_, 0, v_ref_4777_);
                crate::leanh::lean_ctor_set(v___x_4782_, 1, v___x_4781_);
                if v_isShared_4776_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4775_, 0, v___x_4782_);
                    v___x_4784_ = v___x_4775_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4782_);
                    v___x_4784_ = v_reuseFailAlloc_4785_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed(
    mut v_val_4790_: *mut crate::leanh::LeanObject,
    mut v_val_4791_: *mut crate::leanh::LeanObject,
    mut v_x_4792_: *mut crate::leanh::LeanObject,
    mut v___y_4793_: *mut crate::leanh::LeanObject,
    mut v___y_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4796_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0(v_val_4790_, v_val_4791_, v_x_4792_, v___y_4793_, v___y_4794_);
    crate::leanh::lean_dec(v___y_4794_);
    crate::leanh::lean_dec_ref(v___y_4793_);
    crate::leanh::lean_dec(v_val_4791_);
    crate::leanh::lean_dec_ref(v_val_4790_);
    return v_res_4796_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4799_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
    v___x_4800_ = crate::leanh::lean_unsigned_to_nat(44);
    v___x_4801_ = crate::leanh::lean_unsigned_to_nat(209);
    v___x_4802_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__1;
    v___x_4803_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10;
    v___x_4804_ = l_mkPanicMessageWithDecl(
        v___x_4803_,
        v___x_4802_,
        v___x_4801_,
        v___x_4800_,
        v___x_4799_,
    );
    return v___x_4804_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(
    mut v___x_4805_: *mut crate::leanh::LeanObject,
    mut v___x_4806_: *mut crate::leanh::LeanObject,
    mut v___x_4807_: *mut crate::leanh::LeanObject,
    mut v___x_4808_: *mut crate::leanh::LeanObject,
    mut v___x_4809_: u8,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
    mut v___y_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4823_: u8 = 0;
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4829_: u8 = 0;
    let mut v_cancelTk_x3f_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4851_: u8 = 0;
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4855_: u8 = 0;
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4813_ = lean_io_promise_new();
                v___x_4814_ = l_Lean_Server_Test_Cancel_cmdOnceRef;
                v___x_4815_ = lean_st_ref_take(v___x_4814_);
                if crate::leanh::lean_obj_tag(v___x_4815_) == 0 {
                    v___x_4858_ = l_IO_Promise_result_x21___redArg(v___x_4813_);
                    v___y_4817_ = v___x_4858_;
                    state = 1;
                    continue;
                } else {
                    v_val_4859_ = crate::leanh::lean_ctor_get(v___x_4815_, 0);
                    crate::leanh::lean_inc(v_val_4859_);
                    v___y_4817_ = v_val_4859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4818_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4818_, 0, v___y_4817_);
                v___x_4819_ = lean_st_ref_set(v___x_4814_, v___x_4818_);
                if crate::leanh::lean_obj_tag(v___x_4815_) == 1 {
                    crate::leanh::lean_dec(v___x_4813_);
                    crate::leanh::lean_dec_ref(v___y_4810_);
                    crate::leanh::lean_dec_ref(v___x_4808_);
                    crate::leanh::lean_dec_ref(v___x_4807_);
                    crate::leanh::lean_dec_ref(v___x_4806_);
                    crate::leanh::lean_dec_ref(v___x_4805_);
                    v_val_4820_ = crate::leanh::lean_ctor_get(v___x_4815_, 0);
                    v_isSharedCheck_4829_ = (!crate::leanh::lean_is_exclusive(v___x_4815_)) as u8;
                    if v_isSharedCheck_4829_ == 0 {
                        v___x_4822_ = v___x_4815_;
                        v_isShared_4823_ = v_isSharedCheck_4829_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4820_);
                        crate::leanh::lean_dec(v___x_4815_);
                        v___x_4822_ = crate::leanh::lean_box(0);
                        v_isShared_4823_ = v_isSharedCheck_4829_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4815_);
                    v_cancelTk_x3f_4830_ = crate::leanh::lean_ctor_get(v___y_4810_, 12);
                    if crate::leanh::lean_obj_tag(v_cancelTk_x3f_4830_) == 1 {
                        v_val_4831_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_4830_, 0);
                        crate::leanh::lean_inc(v_val_4831_);
                        v___f_4832_ = crate::leanh::lean_alloc_closure(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__0___boxed as *mut core::ffi::c_void, 6, 2);
                        crate::leanh::lean_closure_set(v___f_4832_, 0, v_val_4831_);
                        crate::leanh::lean_closure_set(v___f_4832_, 1, v___x_4813_);
                        v___x_4833_ = crate::leanh::lean_box(0);
                        v___x_4834_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__0;
                        v___x_4835_ = l_Lean_Name_mkStr5(
                            v___x_4805_,
                            v___x_4806_,
                            v___x_4807_,
                            v___x_4808_,
                            v___x_4834_,
                        );
                        v___x_4836_ = l_Lean_Name_toString(v___x_4835_, v___x_4809_);
                        v___x_4837_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(
                            v___f_4832_,
                            v___x_4833_,
                            v___x_4836_,
                            v___y_4810_,
                            v___y_4811_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4837_) == 0 {
                            v_a_4838_ = crate::leanh::lean_ctor_get(v___x_4837_, 0);
                            crate::leanh::lean_inc(v_a_4838_);
                            crate::leanh::lean_dec_ref_known(v___x_4837_, 1);
                            v___x_4839_ = crate::leanh::lean_box(0);
                            v___x_4840_ = crate::leanh::lean_apply_1(v_a_4838_, v___x_4839_);
                            v___x_4841_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4842_ = lean_io_as_task(v___x_4840_, v___x_4841_);
                            v___x_4843_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__main__cancel__once__async__1___closed__2);
                            crate::leanh::lean_inc_ref(v_cancelTk_x3f_4830_);
                            v___x_4844_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4844_, 0, v___x_4833_);
                            crate::leanh::lean_ctor_set(v___x_4844_, 1, v___x_4843_);
                            crate::leanh::lean_ctor_set(v___x_4844_, 2, v_cancelTk_x3f_4830_);
                            crate::leanh::lean_ctor_set(v___x_4844_, 3, v___x_4842_);
                            v___x_4845_ =
                                l_Lean_Core_logSnapshotTask___redArg(v___x_4844_, v___y_4811_);
                            if crate::leanh::lean_obj_tag(v___x_4845_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4845_, 1);
                                v___x_4846_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__2);
                                v___x_4847_ = l_Lean_logInfo___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__2(v___x_4846_, v___y_4810_, v___y_4811_);
                                crate::leanh::lean_dec_ref(v___y_4810_);
                                return v___x_4847_;
                            } else {
                                crate::leanh::lean_dec_ref(v___y_4810_);
                                return v___x_4845_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_4810_);
                            v_a_4848_ = crate::leanh::lean_ctor_get(v___x_4837_, 0);
                            v_isSharedCheck_4855_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4837_)) as u8;
                            if v_isSharedCheck_4855_ == 0 {
                                v___x_4850_ = v___x_4837_;
                                v_isShared_4851_ = v_isSharedCheck_4855_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4848_);
                                crate::leanh::lean_dec(v___x_4837_);
                                v___x_4850_ = crate::leanh::lean_box(0);
                                v_isShared_4851_ = v_isSharedCheck_4855_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4813_);
                        crate::leanh::lean_dec_ref(v___x_4808_);
                        crate::leanh::lean_dec_ref(v___x_4807_);
                        crate::leanh::lean_dec_ref(v___x_4806_);
                        crate::leanh::lean_dec_ref(v___x_4805_);
                        v___x_4856_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___closed__2);
                        v___x_4857_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__3(v___x_4856_, v___y_4810_, v___y_4811_);
                        crate::leanh::lean_dec_ref(v___y_4810_);
                        return v___x_4857_;
                    }
                }
            }
            2 => {
                v___x_4824_ = lean_io_wait(v_val_4820_);
                crate::leanh::lean_dec(v___x_4824_);
                v___x_4825_ = crate::leanh::lean_box(0);
                if v_isShared_4823_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4822_, 0);
                    crate::leanh::lean_ctor_set(v___x_4822_, 0, v___x_4825_);
                    v___x_4827_ = v___x_4822_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4825_);
                    v___x_4827_ = v_reuseFailAlloc_4828_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4827_;
            }
            4 => {
                if v_isShared_4851_ == 0 {
                    v___x_4853_ = v___x_4850_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4854_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
                    v___x_4853_ = v_reuseFailAlloc_4854_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed(
    mut v___x_4860_: *mut crate::leanh::LeanObject,
    mut v___x_4861_: *mut crate::leanh::LeanObject,
    mut v___x_4862_: *mut crate::leanh::LeanObject,
    mut v___x_4863_: *mut crate::leanh::LeanObject,
    mut v___x_4864_: *mut crate::leanh::LeanObject,
    mut v___y_4865_: *mut crate::leanh::LeanObject,
    mut v___y_4866_: *mut crate::leanh::LeanObject,
    mut v___y_4867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7582__boxed_4868_: u8 = 0;
    let mut v_res_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7582__boxed_4868_ = (crate::leanh::lean_unbox(v___x_4864_) as u8);
    v_res_4869_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1(v___x_4860_, v___x_4861_, v___x_4862_, v___x_4863_, v___x_7582__boxed_4868_, v___y_4865_, v___y_4866_);
    crate::leanh::lean_dec(v___y_4866_);
    return v_res_4869_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(
    mut v_x_4870_: *mut crate::leanh::LeanObject,
    mut v_a_4871_: *mut crate::leanh::LeanObject,
    mut v_a_4872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: u8 = 0;
    v___x_4874_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__0;
    v___x_4875_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__1;
    v___x_4876_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__2;
    v___x_4877_ = l_Lean_Server_Test_Cancel_tacticWait__for__cancel__once___closed__3;
    v___x_4878_ = l_Lean_Server_Test_Cancel_commandWait__for__cancel__once__command___00__closed__1;
    v___x_4879_ = l_Lean_Syntax_isOfKind(v_x_4870_, v___x_4878_);
    if v___x_4879_ == 0 {
        let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__0___redArg();
        return v___x_4880_;
    } else {
        let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4881_ = crate::leanh::lean_box((v___x_4879_) as usize);
        v___f_4882_ = crate::leanh::lean_alloc_closure(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___lam__1___boxed as *mut core::ffi::c_void, 8, 5);
        crate::leanh::lean_closure_set(v___f_4882_, 0, v___x_4874_);
        crate::leanh::lean_closure_set(v___f_4882_, 1, v___x_4875_);
        crate::leanh::lean_closure_set(v___f_4882_, 2, v___x_4876_);
        crate::leanh::lean_closure_set(v___f_4882_, 3, v___x_4877_);
        crate::leanh::lean_closure_set(v___f_4882_, 4, v___x_4881_);
        v___x_4883_ = l_Lean_Elab_Command_liftCoreM___redArg(v___f_4882_, v_a_4871_, v_a_4872_);
        return v___x_4883_;
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1___boxed(
    mut v_x_4884_: *mut crate::leanh::LeanObject,
    mut v_a_4885_: *mut crate::leanh::LeanObject,
    mut v_a_4886_: *mut crate::leanh::LeanObject,
    mut v_a_4887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4888_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1(v_x_4884_, v_a_4885_, v_a_4886_);
    crate::leanh::lean_dec(v_a_4886_);
    crate::leanh::lean_dec_ref(v_a_4885_);
    return v_res_4888_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(
    mut v_val_4889_: *mut crate::leanh::LeanObject,
    mut v_inst_4890_: *mut crate::leanh::LeanObject,
    mut v_a_4891_: *mut crate::leanh::LeanObject,
    mut v___y_4892_: *mut crate::leanh::LeanObject,
    mut v___y_4893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4895_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___redArg(v_val_4889_);
    return v___x_4895_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1___boxed(
    mut v_val_4896_: *mut crate::leanh::LeanObject,
    mut v_inst_4897_: *mut crate::leanh::LeanObject,
    mut v_a_4898_: *mut crate::leanh::LeanObject,
    mut v___y_4899_: *mut crate::leanh::LeanObject,
    mut v___y_4900_: *mut crate::leanh::LeanObject,
    mut v___y_4901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4902_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__commandWait__for__cancel__once__command____1_spec__1(v_val_4896_, v_inst_4897_, v_a_4898_, v___y_4899_, v___y_4900_);
    crate::leanh::lean_dec(v___y_4900_);
    crate::leanh::lean_dec_ref(v___y_4899_);
    crate::leanh::lean_dec_ref(v_val_4896_);
    return v_res_4902_;
}
pub unsafe fn _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4903_ = crate::leanh::lean_box(0);
    v___x_4904_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4905_ = lean_mk_array(v___x_4904_, v___x_4903_);
    return v___x_4905_;
}
pub unsafe fn _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4906_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__0_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_);
    v___x_4907_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4908_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4908_, 0, v___x_4907_);
    crate::leanh::lean_ctor_set(v___x_4908_, 1, v___x_4906_);
    return v___x_4908_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4910_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_);
    v___x_4911_ = lean_st_mk_ref(v___x_4910_);
    v___x_4912_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4912_, 0, v___x_4911_);
    return v___x_4912_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2____boxed(
    mut v_a_4913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4914_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_();
    return v_res_4914_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(
    mut v_a_4915_: *mut crate::leanh::LeanObject,
    mut v_b_4916_: *mut crate::leanh::LeanObject,
    mut v_x_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4923_: u8 = 0;
    let mut v___x_4924_: u8 = 0;
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4917_) == 0 {
                    crate::leanh::lean_dec(v_b_4916_);
                    crate::leanh::lean_dec_ref(v_a_4915_);
                    return v_x_4917_;
                } else {
                    v_key_4918_ = crate::leanh::lean_ctor_get(v_x_4917_, 0);
                    v_value_4919_ = crate::leanh::lean_ctor_get(v_x_4917_, 1);
                    v_tail_4920_ = crate::leanh::lean_ctor_get(v_x_4917_, 2);
                    v_isSharedCheck_4932_ = (!crate::leanh::lean_is_exclusive(v_x_4917_)) as u8;
                    if v_isSharedCheck_4932_ == 0 {
                        v___x_4922_ = v_x_4917_;
                        v_isShared_4923_ = v_isSharedCheck_4932_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4920_);
                        crate::leanh::lean_inc(v_value_4919_);
                        crate::leanh::lean_inc(v_key_4918_);
                        crate::leanh::lean_dec(v_x_4917_);
                        v___x_4922_ = crate::leanh::lean_box(0);
                        v_isShared_4923_ = v_isSharedCheck_4932_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4924_ = lean_string_dec_eq(v_key_4918_, v_a_4915_);
                if v___x_4924_ == 0 {
                    v___x_4925_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(v_a_4915_, v_b_4916_, v_tail_4920_);
                    if v_isShared_4923_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4922_, 2, v___x_4925_);
                        v___x_4927_ = v___x_4922_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4928_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_key_4918_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 1, v_value_4919_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4928_, 2, v___x_4925_);
                        v___x_4927_ = v_reuseFailAlloc_4928_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4919_);
                    crate::leanh::lean_dec(v_key_4918_);
                    if v_isShared_4923_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4922_, 1, v_b_4916_);
                        crate::leanh::lean_ctor_set(v___x_4922_, 0, v_a_4915_);
                        v___x_4930_ = v___x_4922_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4931_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4915_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 1, v_b_4916_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 2, v_tail_4920_);
                        v___x_4930_ = v_reuseFailAlloc_4931_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4927_;
            }
            3 => {
                return v___x_4930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_4933_: *mut crate::leanh::LeanObject,
    mut v_x_4934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4940_: u8 = 0;
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: u64 = 0;
    let mut v___x_4943_: u64 = 0;
    let mut v___x_4944_: u64 = 0;
    let mut v_fold_4945_: u64 = 0;
    let mut v___x_4946_: u64 = 0;
    let mut v___x_4947_: u64 = 0;
    let mut v___x_4948_: u64 = 0;
    let mut v___x_4949_: usize = 0;
    let mut v___x_4950_: usize = 0;
    let mut v___x_4951_: usize = 0;
    let mut v___x_4952_: usize = 0;
    let mut v___x_4953_: usize = 0;
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4934_) == 0 {
                    return v_x_4933_;
                } else {
                    v_key_4935_ = crate::leanh::lean_ctor_get(v_x_4934_, 0);
                    v_value_4936_ = crate::leanh::lean_ctor_get(v_x_4934_, 1);
                    v_tail_4937_ = crate::leanh::lean_ctor_get(v_x_4934_, 2);
                    v_isSharedCheck_4960_ = (!crate::leanh::lean_is_exclusive(v_x_4934_)) as u8;
                    if v_isSharedCheck_4960_ == 0 {
                        v___x_4939_ = v_x_4934_;
                        v_isShared_4940_ = v_isSharedCheck_4960_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4937_);
                        crate::leanh::lean_inc(v_value_4936_);
                        crate::leanh::lean_inc(v_key_4935_);
                        crate::leanh::lean_dec(v_x_4934_);
                        v___x_4939_ = crate::leanh::lean_box(0);
                        v_isShared_4940_ = v_isSharedCheck_4960_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4941_ = lean_array_get_size(v_x_4933_);
                v___x_4942_ = lean_string_hash(v_key_4935_);
                v___x_4943_ = 32u64;
                v___x_4944_ = lean_uint64_shift_right(v___x_4942_, v___x_4943_);
                v_fold_4945_ = lean_uint64_xor(v___x_4942_, v___x_4944_);
                v___x_4946_ = 16u64;
                v___x_4947_ = lean_uint64_shift_right(v_fold_4945_, v___x_4946_);
                v___x_4948_ = lean_uint64_xor(v_fold_4945_, v___x_4947_);
                v___x_4949_ = lean_uint64_to_usize(v___x_4948_);
                v___x_4950_ = lean_usize_of_nat(v___x_4941_);
                v___x_4951_ = 1usize;
                v___x_4952_ = lean_usize_sub(v___x_4950_, v___x_4951_);
                v___x_4953_ = lean_usize_land(v___x_4949_, v___x_4952_);
                v___x_4954_ = lean_array_uget_borrowed(v_x_4933_, v___x_4953_);
                crate::leanh::lean_inc(v___x_4954_);
                if v_isShared_4940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4939_, 2, v___x_4954_);
                    v___x_4956_ = v___x_4939_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4959_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_key_4935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 1, v_value_4936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 2, v___x_4954_);
                    v___x_4956_ = v_reuseFailAlloc_4959_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4957_ = lean_array_uset(v_x_4933_, v___x_4953_, v___x_4956_);
                v_x_4933_ = v___x_4957_;
                v_x_4934_ = v_tail_4937_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(
    mut v_i_4961_: *mut crate::leanh::LeanObject,
    mut v_source_4962_: *mut crate::leanh::LeanObject,
    mut v_target_4963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: u8 = 0;
    let mut v_es_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4964_ = lean_array_get_size(v_source_4962_);
                v___x_4965_ = lean_nat_dec_lt(v_i_4961_, v___x_4964_);
                if v___x_4965_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4962_);
                    crate::leanh::lean_dec(v_i_4961_);
                    return v_target_4963_;
                } else {
                    v_es_4966_ = lean_array_fget(v_source_4962_, v_i_4961_);
                    v___x_4967_ = crate::leanh::lean_box(0);
                    v_source_4968_ = lean_array_fset(v_source_4962_, v_i_4961_, v___x_4967_);
                    v_target_4969_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(v_target_4963_, v_es_4966_);
                    v___x_4970_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4971_ = lean_nat_add(v_i_4961_, v___x_4970_);
                    crate::leanh::lean_dec(v_i_4961_);
                    v_i_4961_ = v___x_4971_;
                    v_source_4962_ = v_source_4968_;
                    v_target_4963_ = v_target_4969_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(
    mut v_data_4973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4974_ = lean_array_get_size(v_data_4973_);
    v___x_4975_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4976_ = lean_nat_mul(v___x_4974_, v___x_4975_);
    v___x_4977_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4978_ = crate::leanh::lean_box(0);
    v___x_4979_ = lean_mk_array(v_nbuckets_4976_, v___x_4978_);
    v___x_4980_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(v___x_4977_, v_data_4973_, v___x_4979_);
    return v___x_4980_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(
    mut v_a_4981_: *mut crate::leanh::LeanObject,
    mut v_x_4982_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4983_: u8 = 0;
    let mut v_key_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4982_) == 0 {
                    v___x_4983_ = 0;
                    return v___x_4983_;
                } else {
                    v_key_4984_ = crate::leanh::lean_ctor_get(v_x_4982_, 0);
                    v_tail_4985_ = crate::leanh::lean_ctor_get(v_x_4982_, 2);
                    v___x_4986_ = lean_string_dec_eq(v_key_4984_, v_a_4981_);
                    if v___x_4986_ == 0 {
                        v_x_4982_ = v_tail_4985_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4986_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg___boxed(
    mut v_a_4988_: *mut crate::leanh::LeanObject,
    mut v_x_4989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4990_: u8 = 0;
    let mut v_r_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_4988_, v_x_4989_);
    crate::leanh::lean_dec(v_x_4989_);
    crate::leanh::lean_dec_ref(v_a_4988_);
    v_r_4991_ = crate::leanh::lean_box((v_res_4990_) as usize);
    return v_r_4991_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(
    mut v_m_4992_: *mut crate::leanh::LeanObject,
    mut v_a_4993_: *mut crate::leanh::LeanObject,
    mut v_b_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4999_: u8 = 0;
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: u64 = 0;
    let mut v___x_5002_: u64 = 0;
    let mut v___x_5003_: u64 = 0;
    let mut v_fold_5004_: u64 = 0;
    let mut v___x_5005_: u64 = 0;
    let mut v___x_5006_: u64 = 0;
    let mut v___x_5007_: u64 = 0;
    let mut v___x_5008_: usize = 0;
    let mut v___x_5009_: usize = 0;
    let mut v___x_5010_: usize = 0;
    let mut v___x_5011_: usize = 0;
    let mut v___x_5012_: usize = 0;
    let mut v_bkt_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: u8 = 0;
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: u8 = 0;
    let mut v_val_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4995_ = crate::leanh::lean_ctor_get(v_m_4992_, 0);
                v_buckets_4996_ = crate::leanh::lean_ctor_get(v_m_4992_, 1);
                v_isSharedCheck_5039_ = (!crate::leanh::lean_is_exclusive(v_m_4992_)) as u8;
                if v_isSharedCheck_5039_ == 0 {
                    v___x_4998_ = v_m_4992_;
                    v_isShared_4999_ = v_isSharedCheck_5039_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4996_);
                    crate::leanh::lean_inc(v_size_4995_);
                    crate::leanh::lean_dec(v_m_4992_);
                    v___x_4998_ = crate::leanh::lean_box(0);
                    v_isShared_4999_ = v_isSharedCheck_5039_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5000_ = lean_array_get_size(v_buckets_4996_);
                v___x_5001_ = lean_string_hash(v_a_4993_);
                v___x_5002_ = 32u64;
                v___x_5003_ = lean_uint64_shift_right(v___x_5001_, v___x_5002_);
                v_fold_5004_ = lean_uint64_xor(v___x_5001_, v___x_5003_);
                v___x_5005_ = 16u64;
                v___x_5006_ = lean_uint64_shift_right(v_fold_5004_, v___x_5005_);
                v___x_5007_ = lean_uint64_xor(v_fold_5004_, v___x_5006_);
                v___x_5008_ = lean_uint64_to_usize(v___x_5007_);
                v___x_5009_ = lean_usize_of_nat(v___x_5000_);
                v___x_5010_ = 1usize;
                v___x_5011_ = lean_usize_sub(v___x_5009_, v___x_5010_);
                v___x_5012_ = lean_usize_land(v___x_5008_, v___x_5011_);
                v_bkt_5013_ = lean_array_uget_borrowed(v_buckets_4996_, v___x_5012_);
                v___x_5014_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_4993_, v_bkt_5013_);
                if v___x_5014_ == 0 {
                    v___x_5015_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5016_ = lean_nat_add(v_size_4995_, v___x_5015_);
                    crate::leanh::lean_dec(v_size_4995_);
                    crate::leanh::lean_inc(v_bkt_5013_);
                    v___x_5017_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5017_, 0, v_a_4993_);
                    crate::leanh::lean_ctor_set(v___x_5017_, 1, v_b_4994_);
                    crate::leanh::lean_ctor_set(v___x_5017_, 2, v_bkt_5013_);
                    v_buckets_x27_5018_ =
                        lean_array_uset(v_buckets_4996_, v___x_5012_, v___x_5017_);
                    v___x_5019_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5020_ = lean_nat_mul(v_size_x27_5016_, v___x_5019_);
                    v___x_5021_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_5022_ = lean_nat_div(v___x_5020_, v___x_5021_);
                    crate::leanh::lean_dec(v___x_5020_);
                    v___x_5023_ = lean_array_get_size(v_buckets_x27_5018_);
                    v___x_5024_ = lean_nat_dec_le(v___x_5022_, v___x_5023_);
                    crate::leanh::lean_dec(v___x_5022_);
                    if v___x_5024_ == 0 {
                        v_val_5025_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(v_buckets_x27_5018_);
                        if v_isShared_4999_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4998_, 1, v_val_5025_);
                            crate::leanh::lean_ctor_set(v___x_4998_, 0, v_size_x27_5016_);
                            v___x_5027_ = v___x_4998_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5028_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5028_,
                                0,
                                v_size_x27_5016_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5028_, 1, v_val_5025_);
                            v___x_5027_ = v_reuseFailAlloc_5028_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4999_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4998_, 1, v_buckets_x27_5018_);
                            crate::leanh::lean_ctor_set(v___x_4998_, 0, v_size_x27_5016_);
                            v___x_5030_ = v___x_4998_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5031_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5031_,
                                0,
                                v_size_x27_5016_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5031_,
                                1,
                                v_buckets_x27_5018_,
                            );
                            v___x_5030_ = v_reuseFailAlloc_5031_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_5013_);
                    v___x_5032_ = crate::leanh::lean_box(0);
                    v_buckets_x27_5033_ =
                        lean_array_uset(v_buckets_4996_, v___x_5012_, v___x_5032_);
                    v___x_5034_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(v_a_4993_, v_b_4994_, v_bkt_5013_);
                    v___x_5035_ = lean_array_uset(v_buckets_x27_5033_, v___x_5012_, v___x_5034_);
                    if v_isShared_4999_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4998_, 1, v___x_5035_);
                        v___x_5037_ = v___x_4998_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5038_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_size_4995_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5038_, 1, v___x_5035_);
                        v___x_5037_ = v_reuseFailAlloc_5038_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5027_;
            }
            3 => {
                return v___x_5030_;
            }
            4 => {
                return v___x_5037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(
    mut v_m_5040_: *mut crate::leanh::LeanObject,
    mut v_a_5041_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: u64 = 0;
    let mut v___x_5045_: u64 = 0;
    let mut v___x_5046_: u64 = 0;
    let mut v_fold_5047_: u64 = 0;
    let mut v___x_5048_: u64 = 0;
    let mut v___x_5049_: u64 = 0;
    let mut v___x_5050_: u64 = 0;
    let mut v___x_5051_: usize = 0;
    let mut v___x_5052_: usize = 0;
    let mut v___x_5053_: usize = 0;
    let mut v___x_5054_: usize = 0;
    let mut v___x_5055_: usize = 0;
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: u8 = 0;
    v_buckets_5042_ = crate::leanh::lean_ctor_get(v_m_5040_, 1);
    v___x_5043_ = lean_array_get_size(v_buckets_5042_);
    v___x_5044_ = lean_string_hash(v_a_5041_);
    v___x_5045_ = 32u64;
    v___x_5046_ = lean_uint64_shift_right(v___x_5044_, v___x_5045_);
    v_fold_5047_ = lean_uint64_xor(v___x_5044_, v___x_5046_);
    v___x_5048_ = 16u64;
    v___x_5049_ = lean_uint64_shift_right(v_fold_5047_, v___x_5048_);
    v___x_5050_ = lean_uint64_xor(v_fold_5047_, v___x_5049_);
    v___x_5051_ = lean_uint64_to_usize(v___x_5050_);
    v___x_5052_ = lean_usize_of_nat(v___x_5043_);
    v___x_5053_ = 1usize;
    v___x_5054_ = lean_usize_sub(v___x_5052_, v___x_5053_);
    v___x_5055_ = lean_usize_land(v___x_5051_, v___x_5054_);
    v___x_5056_ = lean_array_uget_borrowed(v_buckets_5042_, v___x_5055_);
    v___x_5057_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_5041_, v___x_5056_);
    return v___x_5057_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg___boxed(
    mut v_m_5058_: *mut crate::leanh::LeanObject,
    mut v_a_5059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5060_: u8 = 0;
    let mut v_r_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5060_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v_m_5058_, v_a_5059_);
    crate::leanh::lean_dec_ref(v_a_5059_);
    crate::leanh::lean_dec_ref(v_m_5058_);
    v_r_5061_ = crate::leanh::lean_box((v_res_5060_) as usize);
    return v_r_5061_;
}
pub unsafe fn l_Lean_Server_Test_Cancel_mkTestTask(
    mut v_label_5062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: u8 = 0;
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5064_ = lean_io_promise_new();
                v___x_5065_ = l_Lean_Server_Test_Cancel_testTasksRef;
                v___x_5066_ = lean_st_ref_take(v___x_5065_);
                v___x_5071_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v___x_5066_, v_label_5062_);
                if v___x_5071_ == 0 {
                    crate::leanh::lean_inc(v___x_5064_);
                    v___x_5072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5072_, 0, v___x_5064_);
                    v___x_5073_ = lean_io_promise_result_opt(v___x_5064_);
                    crate::leanh::lean_dec(v___x_5064_);
                    v___x_5074_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v___x_5066_, v_label_5062_, v___x_5073_);
                    v_fst_5068_ = v___x_5072_;
                    v_snd_5069_ = v___x_5074_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5064_);
                    crate::leanh::lean_dec_ref(v_label_5062_);
                    v___x_5075_ = crate::leanh::lean_box(0);
                    v_fst_5068_ = v___x_5075_;
                    v_snd_5069_ = v___x_5066_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5070_ = lean_st_ref_set(v___x_5065_, v_snd_5069_);
                return v_fst_5068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel_mkTestTask___boxed(
    mut v_label_5076_: *mut crate::leanh::LeanObject,
    mut v_a_5077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5078_ = l_Lean_Server_Test_Cancel_mkTestTask(v_label_5076_);
    return v_res_5078_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0(
    mut v_00_u03b2_5079_: *mut crate::leanh::LeanObject,
    mut v_m_5080_: *mut crate::leanh::LeanObject,
    mut v_a_5081_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5082_: u8 = 0;
    v___x_5082_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___redArg(v_m_5080_, v_a_5081_);
    return v___x_5082_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0___boxed(
    mut v_00_u03b2_5083_: *mut crate::leanh::LeanObject,
    mut v_m_5084_: *mut crate::leanh::LeanObject,
    mut v_a_5085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5086_: u8 = 0;
    let mut v_r_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5086_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0(v_00_u03b2_5083_, v_m_5084_, v_a_5085_);
    crate::leanh::lean_dec_ref(v_a_5085_);
    crate::leanh::lean_dec_ref(v_m_5084_);
    v_r_5087_ = crate::leanh::lean_box((v_res_5086_) as usize);
    return v_r_5087_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1(
    mut v_00_u03b2_5088_: *mut crate::leanh::LeanObject,
    mut v_m_5089_: *mut crate::leanh::LeanObject,
    mut v_a_5090_: *mut crate::leanh::LeanObject,
    mut v_b_5091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5092_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v_m_5089_, v_a_5090_, v_b_5091_);
    return v___x_5092_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0(
    mut v_00_u03b2_5093_: *mut crate::leanh::LeanObject,
    mut v_a_5094_: *mut crate::leanh::LeanObject,
    mut v_x_5095_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5096_: u8 = 0;
    v___x_5096_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___redArg(v_a_5094_, v_x_5095_);
    return v___x_5096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0___boxed(
    mut v_00_u03b2_5097_: *mut crate::leanh::LeanObject,
    mut v_a_5098_: *mut crate::leanh::LeanObject,
    mut v_x_5099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5100_: u8 = 0;
    let mut v_r_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5100_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_Test_Cancel_mkTestTask_spec__0_spec__0(v_00_u03b2_5097_, v_a_5098_, v_x_5099_);
    crate::leanh::lean_dec(v_x_5099_);
    crate::leanh::lean_dec_ref(v_a_5098_);
    v_r_5101_ = crate::leanh::lean_box((v_res_5100_) as usize);
    return v_r_5101_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2(
    mut v_00_u03b2_5102_: *mut crate::leanh::LeanObject,
    mut v_data_5103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5104_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2___redArg(v_data_5103_);
    return v___x_5104_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3(
    mut v_00_u03b2_5105_: *mut crate::leanh::LeanObject,
    mut v_a_5106_: *mut crate::leanh::LeanObject,
    mut v_b_5107_: *mut crate::leanh::LeanObject,
    mut v_x_5108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5109_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__3___redArg(v_a_5106_, v_b_5107_, v_x_5108_);
    return v___x_5109_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5110_: *mut crate::leanh::LeanObject,
    mut v_i_5111_: *mut crate::leanh::LeanObject,
    mut v_source_5112_: *mut crate::leanh::LeanObject,
    mut v_target_5113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5114_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3___redArg(v_i_5111_, v_source_5112_, v_target_5113_);
    return v___x_5114_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_5115_: *mut crate::leanh::LeanObject,
    mut v_x_5116_: *mut crate::leanh::LeanObject,
    mut v_x_5117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5118_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1_spec__2_spec__3_spec__4___redArg(v_x_5116_, v_x_5117_);
    return v___x_5118_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(
    mut v_a_5144_: *mut crate::leanh::LeanObject,
    mut v_x_5145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5145_) == 0 {
                    v___x_5146_ = crate::leanh::lean_box(0);
                    return v___x_5146_;
                } else {
                    v_key_5147_ = crate::leanh::lean_ctor_get(v_x_5145_, 0);
                    v_value_5148_ = crate::leanh::lean_ctor_get(v_x_5145_, 1);
                    v_tail_5149_ = crate::leanh::lean_ctor_get(v_x_5145_, 2);
                    v___x_5150_ = lean_string_dec_eq(v_key_5147_, v_a_5144_);
                    if v___x_5150_ == 0 {
                        v_x_5145_ = v_tail_5149_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5148_);
                        v___x_5152_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5152_, 0, v_value_5148_);
                        return v___x_5152_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg___boxed(
    mut v_a_5153_: *mut crate::leanh::LeanObject,
    mut v_x_5154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5155_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(v_a_5153_, v_x_5154_);
    crate::leanh::lean_dec(v_x_5154_);
    crate::leanh::lean_dec_ref(v_a_5153_);
    return v_res_5155_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(
    mut v_m_5156_: *mut crate::leanh::LeanObject,
    mut v_a_5157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: u64 = 0;
    let mut v___x_5161_: u64 = 0;
    let mut v___x_5162_: u64 = 0;
    let mut v_fold_5163_: u64 = 0;
    let mut v___x_5164_: u64 = 0;
    let mut v___x_5165_: u64 = 0;
    let mut v___x_5166_: u64 = 0;
    let mut v___x_5167_: usize = 0;
    let mut v___x_5168_: usize = 0;
    let mut v___x_5169_: usize = 0;
    let mut v___x_5170_: usize = 0;
    let mut v___x_5171_: usize = 0;
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5158_ = crate::leanh::lean_ctor_get(v_m_5156_, 1);
    v___x_5159_ = lean_array_get_size(v_buckets_5158_);
    v___x_5160_ = lean_string_hash(v_a_5157_);
    v___x_5161_ = 32u64;
    v___x_5162_ = lean_uint64_shift_right(v___x_5160_, v___x_5161_);
    v_fold_5163_ = lean_uint64_xor(v___x_5160_, v___x_5162_);
    v___x_5164_ = 16u64;
    v___x_5165_ = lean_uint64_shift_right(v_fold_5163_, v___x_5164_);
    v___x_5166_ = lean_uint64_xor(v_fold_5163_, v___x_5165_);
    v___x_5167_ = lean_uint64_to_usize(v___x_5166_);
    v___x_5168_ = lean_usize_of_nat(v___x_5159_);
    v___x_5169_ = 1usize;
    v___x_5170_ = lean_usize_sub(v___x_5168_, v___x_5169_);
    v___x_5171_ = lean_usize_land(v___x_5167_, v___x_5170_);
    v___x_5172_ = lean_array_uget_borrowed(v_buckets_5158_, v___x_5171_);
    v___x_5173_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(v_a_5157_, v___x_5172_);
    return v___x_5173_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg___boxed(
    mut v_m_5174_: *mut crate::leanh::LeanObject,
    mut v_a_5175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_m_5174_, v_a_5175_);
    crate::leanh::lean_dec_ref(v_a_5175_);
    crate::leanh::lean_dec_ref(v_m_5174_);
    return v_res_5176_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(
    mut v_x_5180_: *mut crate::leanh::LeanObject,
    mut v_a_5181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: u8 = 0;
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5198_: u8 = 0;
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut v_a_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5206_: u8 = 0;
    let mut v_ref_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v_val_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5219_: u8 = 0;
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5233_: u8 = 0;
    let mut v_a_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5237_: u8 = 0;
    let mut v_ref_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5248_: u8 = 0;
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5256_: u8 = 0;
    let mut v_unused_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5183_ = l_Lean_Server_Test_Cancel_tacticWait__for__test__task___00__closed__1;
                crate::leanh::lean_inc(v_x_5180_);
                v___x_5184_ = l_Lean_Syntax_isOfKind(v_x_5180_, v___x_5183_);
                if v___x_5184_ == 0 {
                    crate::leanh::lean_dec(v_x_5180_);
                    v___x_5185_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
                    return v___x_5185_;
                } else {
                    v___x_5186_ = l_Lean_Server_Test_Cancel_testTasksRef;
                    v___x_5187_ = lean_st_ref_get(v___x_5186_);
                    v___x_5188_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_label_5189_ = l_Lean_Syntax_getArg(v_x_5180_, v___x_5188_);
                    crate::leanh::lean_dec(v_x_5180_);
                    v_label_5190_ = l_Lean_TSyntax_getString(v_label_5189_);
                    crate::leanh::lean_dec(v_label_5189_);
                    v___x_5191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v___x_5187_, v_label_5190_);
                    crate::leanh::lean_dec(v___x_5187_);
                    if crate::leanh::lean_obj_tag(v___x_5191_) == 0 {
                        v___x_5192_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__0;
                        v___x_5193_ = lean_string_append(v___x_5192_, v_label_5190_);
                        crate::leanh::lean_dec_ref(v_label_5190_);
                        v___x_5194_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_5193_);
                        if crate::leanh::lean_obj_tag(v___x_5194_) == 0 {
                            v_a_5195_ = crate::leanh::lean_ctor_get(v___x_5194_, 0);
                            v_isSharedCheck_5202_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5194_)) as u8;
                            if v_isSharedCheck_5202_ == 0 {
                                v___x_5197_ = v___x_5194_;
                                v_isShared_5198_ = v_isSharedCheck_5202_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5195_);
                                crate::leanh::lean_dec(v___x_5194_);
                                v___x_5197_ = crate::leanh::lean_box(0);
                                v_isShared_5198_ = v_isSharedCheck_5202_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_5203_ = crate::leanh::lean_ctor_get(v___x_5194_, 0);
                            v_isSharedCheck_5215_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5194_)) as u8;
                            if v_isSharedCheck_5215_ == 0 {
                                v___x_5205_ = v___x_5194_;
                                v_isShared_5206_ = v_isSharedCheck_5215_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5203_);
                                crate::leanh::lean_dec(v___x_5194_);
                                v___x_5205_ = crate::leanh::lean_box(0);
                                v_isShared_5206_ = v_isSharedCheck_5215_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_val_5216_ = crate::leanh::lean_ctor_get(v___x_5191_, 0);
                        v_isSharedCheck_5258_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5191_)) as u8;
                        if v_isSharedCheck_5258_ == 0 {
                            v___x_5218_ = v___x_5191_;
                            v_isShared_5219_ = v_isSharedCheck_5258_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5216_);
                            crate::leanh::lean_dec(v___x_5191_);
                            v___x_5218_ = crate::leanh::lean_box(0);
                            v_isShared_5219_ = v_isSharedCheck_5258_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5198_ == 0 {
                    v___x_5200_ = v___x_5197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
                    v___x_5200_ = v_reuseFailAlloc_5201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5200_;
            }
            3 => {
                v_ref_5207_ = crate::leanh::lean_ctor_get(v_a_5181_, 5);
                v___x_5208_ = lean_io_error_to_string(v_a_5203_);
                v___x_5209_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5209_, 0, v___x_5208_);
                v___x_5210_ = l_Lean_MessageData_ofFormat(v___x_5209_);
                crate::leanh::lean_inc(v_ref_5207_);
                v___x_5211_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5211_, 0, v_ref_5207_);
                crate::leanh::lean_ctor_set(v___x_5211_, 1, v___x_5210_);
                if v_isShared_5206_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5205_, 0, v___x_5211_);
                    v___x_5213_ = v___x_5205_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5214_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 0, v___x_5211_);
                    v___x_5213_ = v_reuseFailAlloc_5214_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5213_;
            }
            5 => {
                v___x_5220_ = lean_io_wait(v_val_5216_);
                if crate::leanh::lean_obj_tag(v___x_5220_) == 0 {
                    v___x_5221_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__1;
                    v___x_5222_ = lean_string_append(v___x_5221_, v_label_5190_);
                    crate::leanh::lean_dec_ref(v_label_5190_);
                    v___x_5223_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2;
                    v___x_5224_ = lean_string_append(v___x_5222_, v___x_5223_);
                    v___x_5225_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_5224_);
                    if crate::leanh::lean_obj_tag(v___x_5225_) == 0 {
                        crate::leanh::lean_del_object(v___x_5218_);
                        v_a_5226_ = crate::leanh::lean_ctor_get(v___x_5225_, 0);
                        v_isSharedCheck_5233_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5225_)) as u8;
                        if v_isSharedCheck_5233_ == 0 {
                            v___x_5228_ = v___x_5225_;
                            v_isShared_5229_ = v_isSharedCheck_5233_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5226_);
                            crate::leanh::lean_dec(v___x_5225_);
                            v___x_5228_ = crate::leanh::lean_box(0);
                            v_isShared_5229_ = v_isSharedCheck_5233_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5234_ = crate::leanh::lean_ctor_get(v___x_5225_, 0);
                        v_isSharedCheck_5248_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5225_)) as u8;
                        if v_isSharedCheck_5248_ == 0 {
                            v___x_5236_ = v___x_5225_;
                            v_isShared_5237_ = v_isSharedCheck_5248_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5234_);
                            crate::leanh::lean_dec(v___x_5225_);
                            v___x_5236_ = crate::leanh::lean_box(0);
                            v_isShared_5237_ = v_isSharedCheck_5248_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5218_);
                    crate::leanh::lean_dec_ref(v_label_5190_);
                    v_isSharedCheck_5256_ = (!crate::leanh::lean_is_exclusive(v___x_5220_)) as u8;
                    if v_isSharedCheck_5256_ == 0 {
                        v_unused_5257_ = crate::leanh::lean_ctor_get(v___x_5220_, 0);
                        crate::leanh::lean_dec(v_unused_5257_);
                        v___x_5250_ = v___x_5220_;
                        v_isShared_5251_ = v_isSharedCheck_5256_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5220_);
                        v___x_5250_ = crate::leanh::lean_box(0);
                        v_isShared_5251_ = v_isSharedCheck_5256_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5229_ == 0 {
                    v___x_5231_ = v___x_5228_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
                    v___x_5231_ = v_reuseFailAlloc_5232_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5231_;
            }
            8 => {
                v_ref_5238_ = crate::leanh::lean_ctor_get(v_a_5181_, 5);
                v___x_5239_ = lean_io_error_to_string(v_a_5234_);
                if v_isShared_5219_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5218_, 3);
                    crate::leanh::lean_ctor_set(v___x_5218_, 0, v___x_5239_);
                    v___x_5241_ = v___x_5218_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5247_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5239_);
                    v___x_5241_ = v_reuseFailAlloc_5247_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5242_ = l_Lean_MessageData_ofFormat(v___x_5241_);
                crate::leanh::lean_inc(v_ref_5238_);
                v___x_5243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5243_, 0, v_ref_5238_);
                crate::leanh::lean_ctor_set(v___x_5243_, 1, v___x_5242_);
                if v_isShared_5237_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5236_, 0, v___x_5243_);
                    v___x_5245_ = v___x_5236_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5243_);
                    v___x_5245_ = v_reuseFailAlloc_5246_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5245_;
            }
            11 => {
                v___x_5252_ = crate::leanh::lean_box(0);
                if v_isShared_5251_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5250_, 0);
                    crate::leanh::lean_ctor_set(v___x_5250_, 0, v___x_5252_);
                    v___x_5254_ = v___x_5250_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5252_);
                    v___x_5254_ = v_reuseFailAlloc_5255_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___boxed(
    mut v_x_5259_: *mut crate::leanh::LeanObject,
    mut v_a_5260_: *mut crate::leanh::LeanObject,
    mut v_a_5261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5262_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(v_x_5259_, v_a_5260_);
    crate::leanh::lean_dec_ref(v_a_5260_);
    return v_res_5262_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1(
    mut v_x_5263_: *mut crate::leanh::LeanObject,
    mut v_a_5264_: *mut crate::leanh::LeanObject,
    mut v_a_5265_: *mut crate::leanh::LeanObject,
    mut v_a_5266_: *mut crate::leanh::LeanObject,
    mut v_a_5267_: *mut crate::leanh::LeanObject,
    mut v_a_5268_: *mut crate::leanh::LeanObject,
    mut v_a_5269_: *mut crate::leanh::LeanObject,
    mut v_a_5270_: *mut crate::leanh::LeanObject,
    mut v_a_5271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5273_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg(v_x_5263_, v_a_5270_);
    return v___x_5273_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___boxed(
    mut v_x_5274_: *mut crate::leanh::LeanObject,
    mut v_a_5275_: *mut crate::leanh::LeanObject,
    mut v_a_5276_: *mut crate::leanh::LeanObject,
    mut v_a_5277_: *mut crate::leanh::LeanObject,
    mut v_a_5278_: *mut crate::leanh::LeanObject,
    mut v_a_5279_: *mut crate::leanh::LeanObject,
    mut v_a_5280_: *mut crate::leanh::LeanObject,
    mut v_a_5281_: *mut crate::leanh::LeanObject,
    mut v_a_5282_: *mut crate::leanh::LeanObject,
    mut v_a_5283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5284_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1(v_x_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_);
    crate::leanh::lean_dec(v_a_5282_);
    crate::leanh::lean_dec_ref(v_a_5281_);
    crate::leanh::lean_dec(v_a_5280_);
    crate::leanh::lean_dec_ref(v_a_5279_);
    crate::leanh::lean_dec(v_a_5278_);
    crate::leanh::lean_dec_ref(v_a_5277_);
    crate::leanh::lean_dec(v_a_5276_);
    crate::leanh::lean_dec_ref(v_a_5275_);
    return v_res_5284_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0(
    mut v_00_u03b2_5285_: *mut crate::leanh::LeanObject,
    mut v_m_5286_: *mut crate::leanh::LeanObject,
    mut v_a_5287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5288_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v_m_5286_, v_a_5287_);
    return v___x_5288_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___boxed(
    mut v_00_u03b2_5289_: *mut crate::leanh::LeanObject,
    mut v_m_5290_: *mut crate::leanh::LeanObject,
    mut v_a_5291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5292_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0(v_00_u03b2_5289_, v_m_5290_, v_a_5291_);
    crate::leanh::lean_dec_ref(v_a_5291_);
    crate::leanh::lean_dec_ref(v_m_5290_);
    return v_res_5292_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0(
    mut v_00_u03b2_5293_: *mut crate::leanh::LeanObject,
    mut v_a_5294_: *mut crate::leanh::LeanObject,
    mut v_x_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5296_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___redArg(v_a_5294_, v_x_5295_);
    return v___x_5296_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0___boxed(
    mut v_00_u03b2_5297_: *mut crate::leanh::LeanObject,
    mut v_a_5298_: *mut crate::leanh::LeanObject,
    mut v_x_5299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5300_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0_spec__0(v_00_u03b2_5297_, v_a_5298_, v_x_5299_);
    crate::leanh::lean_dec(v_x_5299_);
    crate::leanh::lean_dec_ref(v_a_5298_);
    return v_res_5300_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5302_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2__once), _init_l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn___closed__1_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_);
    v___x_5303_ = lean_st_mk_ref(v___x_5302_);
    v___x_5304_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5304_, 0, v___x_5303_);
    return v___x_5304_;
}
pub unsafe fn l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2____boxed(
    mut v_a_5305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5306_ = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_();
    return v_res_5306_;
}
pub unsafe fn l_Lean_Server_Test_Cancel_getSyncPromise(
    mut v_label_5307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5309_ = lean_io_promise_new();
                v___x_5310_ = l_Lean_Server_Test_Cancel_syncPromisesRef;
                v___x_5311_ = lean_st_ref_take(v___x_5310_);
                v___x_5316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v___x_5311_, v_label_5307_);
                if crate::leanh::lean_obj_tag(v___x_5316_) == 0 {
                    crate::leanh::lean_inc(v___x_5309_);
                    v___x_5317_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Server_Test_Cancel_mkTestTask_spec__1___redArg(v___x_5311_, v_label_5307_, v___x_5309_);
                    v_fst_5313_ = v___x_5309_;
                    v_snd_5314_ = v___x_5317_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5309_);
                    crate::leanh::lean_dec_ref(v_label_5307_);
                    v_val_5318_ = crate::leanh::lean_ctor_get(v___x_5316_, 0);
                    crate::leanh::lean_inc(v_val_5318_);
                    crate::leanh::lean_dec_ref_known(v___x_5316_, 1);
                    v_fst_5313_ = v_val_5318_;
                    v_snd_5314_ = v___x_5311_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5315_ = lean_st_ref_set(v___x_5310_, v_snd_5314_);
                return v_fst_5313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel_getSyncPromise___boxed(
    mut v_label_5319_: *mut crate::leanh::LeanObject,
    mut v_a_5320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5321_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_label_5319_);
    return v_res_5321_;
}
pub unsafe fn l_Lean_Server_Test_Cancel_resolveSyncPromise(
    mut v_label_5322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5324_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_label_5322_);
    v___x_5325_ = crate::leanh::lean_box(0);
    v___x_5326_ = lean_io_promise_resolve(v___x_5325_, v___x_5324_);
    crate::leanh::lean_dec(v___x_5324_);
    return v___x_5326_;
}
pub unsafe fn l_Lean_Server_Test_Cancel_resolveSyncPromise___boxed(
    mut v_label_5327_: *mut crate::leanh::LeanObject,
    mut v_a_5328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5329_ = l_Lean_Server_Test_Cancel_resolveSyncPromise(v_label_5327_);
    return v_res_5329_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(
    mut v_x_5351_: *mut crate::leanh::LeanObject,
    mut v_a_5352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: u8 = 0;
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lbl_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5371_: u8 = 0;
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut v_a_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5379_: u8 = 0;
    let mut v_ref_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5388_: u8 = 0;
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5391_: u8 = 0;
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5396_: u8 = 0;
    let mut v_unused_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5354_ = l_Lean_Server_Test_Cancel_tacticWait__for__sync___00__closed__1;
                crate::leanh::lean_inc(v_x_5351_);
                v___x_5355_ = l_Lean_Syntax_isOfKind(v_x_5351_, v___x_5354_);
                if v___x_5355_ == 0 {
                    crate::leanh::lean_dec(v_x_5351_);
                    v___x_5356_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
                    return v___x_5356_;
                } else {
                    v___x_5357_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_label_5358_ = l_Lean_Syntax_getArg(v_x_5351_, v___x_5357_);
                    crate::leanh::lean_dec(v_x_5351_);
                    v_lbl_5359_ = l_Lean_TSyntax_getString(v_label_5358_);
                    crate::leanh::lean_dec(v_label_5358_);
                    crate::leanh::lean_inc_ref(v_lbl_5359_);
                    v___x_5360_ = l_Lean_Server_Test_Cancel_getSyncPromise(v_lbl_5359_);
                    v___x_5361_ = lean_io_promise_result_opt(v___x_5360_);
                    crate::leanh::lean_dec(v___x_5360_);
                    v___x_5362_ = lean_io_wait(v___x_5361_);
                    if crate::leanh::lean_obj_tag(v___x_5362_) == 0 {
                        v___x_5363_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___closed__0;
                        v___x_5364_ = lean_string_append(v___x_5363_, v_lbl_5359_);
                        crate::leanh::lean_dec_ref(v_lbl_5359_);
                        v___x_5365_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1___redArg___closed__2;
                        v___x_5366_ = lean_string_append(v___x_5364_, v___x_5365_);
                        v___x_5367_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_5366_);
                        if crate::leanh::lean_obj_tag(v___x_5367_) == 0 {
                            v_a_5368_ = crate::leanh::lean_ctor_get(v___x_5367_, 0);
                            v_isSharedCheck_5375_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5367_)) as u8;
                            if v_isSharedCheck_5375_ == 0 {
                                v___x_5370_ = v___x_5367_;
                                v_isShared_5371_ = v_isSharedCheck_5375_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5368_);
                                crate::leanh::lean_dec(v___x_5367_);
                                v___x_5370_ = crate::leanh::lean_box(0);
                                v_isShared_5371_ = v_isSharedCheck_5375_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_5376_ = crate::leanh::lean_ctor_get(v___x_5367_, 0);
                            v_isSharedCheck_5388_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5367_)) as u8;
                            if v_isSharedCheck_5388_ == 0 {
                                v___x_5378_ = v___x_5367_;
                                v_isShared_5379_ = v_isSharedCheck_5388_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5376_);
                                crate::leanh::lean_dec(v___x_5367_);
                                v___x_5378_ = crate::leanh::lean_box(0);
                                v_isShared_5379_ = v_isSharedCheck_5388_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_lbl_5359_);
                        v_isSharedCheck_5396_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5362_)) as u8;
                        if v_isSharedCheck_5396_ == 0 {
                            v_unused_5397_ = crate::leanh::lean_ctor_get(v___x_5362_, 0);
                            crate::leanh::lean_dec(v_unused_5397_);
                            v___x_5390_ = v___x_5362_;
                            v_isShared_5391_ = v_isSharedCheck_5396_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5362_);
                            v___x_5390_ = crate::leanh::lean_box(0);
                            v_isShared_5391_ = v_isSharedCheck_5396_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5371_ == 0 {
                    v___x_5373_ = v___x_5370_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
                    v___x_5373_ = v_reuseFailAlloc_5374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5373_;
            }
            3 => {
                v_ref_5380_ = crate::leanh::lean_ctor_get(v_a_5352_, 5);
                v___x_5381_ = lean_io_error_to_string(v_a_5376_);
                v___x_5382_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5382_, 0, v___x_5381_);
                v___x_5383_ = l_Lean_MessageData_ofFormat(v___x_5382_);
                crate::leanh::lean_inc(v_ref_5380_);
                v___x_5384_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5384_, 0, v_ref_5380_);
                crate::leanh::lean_ctor_set(v___x_5384_, 1, v___x_5383_);
                if v_isShared_5379_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5378_, 0, v___x_5384_);
                    v___x_5386_ = v___x_5378_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5387_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5387_, 0, v___x_5384_);
                    v___x_5386_ = v_reuseFailAlloc_5387_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5386_;
            }
            5 => {
                v___x_5392_ = crate::leanh::lean_box(0);
                if v_isShared_5391_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5390_, 0);
                    crate::leanh::lean_ctor_set(v___x_5390_, 0, v___x_5392_);
                    v___x_5394_ = v___x_5390_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5395_, 0, v___x_5392_);
                    v___x_5394_ = v_reuseFailAlloc_5395_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg___boxed(
    mut v_x_5398_: *mut crate::leanh::LeanObject,
    mut v_a_5399_: *mut crate::leanh::LeanObject,
    mut v_a_5400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5401_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(v_x_5398_, v_a_5399_);
    crate::leanh::lean_dec_ref(v_a_5399_);
    return v_res_5401_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1(
    mut v_x_5402_: *mut crate::leanh::LeanObject,
    mut v_a_5403_: *mut crate::leanh::LeanObject,
    mut v_a_5404_: *mut crate::leanh::LeanObject,
    mut v_a_5405_: *mut crate::leanh::LeanObject,
    mut v_a_5406_: *mut crate::leanh::LeanObject,
    mut v_a_5407_: *mut crate::leanh::LeanObject,
    mut v_a_5408_: *mut crate::leanh::LeanObject,
    mut v_a_5409_: *mut crate::leanh::LeanObject,
    mut v_a_5410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5412_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___redArg(v_x_5402_, v_a_5409_);
    return v___x_5412_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1___boxed(
    mut v_x_5413_: *mut crate::leanh::LeanObject,
    mut v_a_5414_: *mut crate::leanh::LeanObject,
    mut v_a_5415_: *mut crate::leanh::LeanObject,
    mut v_a_5416_: *mut crate::leanh::LeanObject,
    mut v_a_5417_: *mut crate::leanh::LeanObject,
    mut v_a_5418_: *mut crate::leanh::LeanObject,
    mut v_a_5419_: *mut crate::leanh::LeanObject,
    mut v_a_5420_: *mut crate::leanh::LeanObject,
    mut v_a_5421_: *mut crate::leanh::LeanObject,
    mut v_a_5422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5423_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__sync____1(v_x_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_);
    crate::leanh::lean_dec(v_a_5421_);
    crate::leanh::lean_dec_ref(v_a_5420_);
    crate::leanh::lean_dec(v_a_5419_);
    crate::leanh::lean_dec_ref(v_a_5418_);
    crate::leanh::lean_dec(v_a_5417_);
    crate::leanh::lean_dec_ref(v_a_5416_);
    crate::leanh::lean_dec(v_a_5415_);
    crate::leanh::lean_dec_ref(v_a_5414_);
    return v_res_5423_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(
    mut v___x_5444_: *mut crate::leanh::LeanObject,
    mut v_val_5445_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5448_ = lean_io_promise_resolve(v___x_5444_, v_val_5445_);
    v___x_5449_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5449_, 0, v___x_5448_);
    return v___x_5449_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0___boxed(
    mut v___x_5450_: *mut crate::leanh::LeanObject,
    mut v_val_5451_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5452_: *mut crate::leanh::LeanObject,
    mut v___y_5453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5454_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_5450_, v_val_5451_, v_a_x3f_5452_);
    crate::leanh::lean_dec(v_a_x3f_5452_);
    crate::leanh::lean_dec(v_val_5451_);
    return v_res_5454_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(
    mut v___y_5455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5458_: u32 = 0;
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: u8 = 0;
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cancelTk_x3f_5461_ = crate::leanh::lean_ctor_get(v___y_5455_, 12);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_5461_) == 1 {
                    v_val_5462_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_5461_, 0);
                    v___x_5463_ = l_IO_CancelToken_isSet(v_val_5462_);
                    if v___x_5463_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_5464_ = l_Lean_throwInterruptException___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__4___redArg();
                        if crate::leanh::lean_obj_tag(v___x_5464_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5464_, 1);
                            state = 1;
                            continue;
                        } else {
                            return v___x_5464_;
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5458_ = 10;
                v___x_5459_ = l_IO_sleep(v___x_5458_);
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg___boxed(
    mut v___y_5465_: *mut crate::leanh::LeanObject,
    mut v___y_5466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5467_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v___y_5465_);
    crate::leanh::lean_dec_ref(v___y_5465_);
    return v_res_5467_;
}
pub unsafe fn _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5469_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__12;
    v___x_5470_ = crate::leanh::lean_unsigned_to_nat(50);
    v___x_5471_ = crate::leanh::lean_unsigned_to_nat(302);
    v___x_5472_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__0;
    v___x_5473_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1___lam__0___closed__10;
    v___x_5474_ = l_mkPanicMessageWithDecl(
        v___x_5473_,
        v___x_5472_,
        v___x_5471_,
        v___x_5470_,
        v___x_5469_,
    );
    return v___x_5474_;
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1(
    mut v_x_5476_: *mut crate::leanh::LeanObject,
    mut v_a_5477_: *mut crate::leanh::LeanObject,
    mut v_a_5478_: *mut crate::leanh::LeanObject,
    mut v_a_5479_: *mut crate::leanh::LeanObject,
    mut v_a_5480_: *mut crate::leanh::LeanObject,
    mut v_a_5481_: *mut crate::leanh::LeanObject,
    mut v_a_5482_: *mut crate::leanh::LeanObject,
    mut v_a_5483_: *mut crate::leanh::LeanObject,
    mut v_a_5484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: u8 = 0;
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lbl_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5499_: u8 = 0;
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5505_: u8 = 0;
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5511_: u8 = 0;
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5528_: u8 = 0;
    let mut v_unused_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5538_: u8 = 0;
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut v_unused_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5547_: u8 = 0;
    let mut v_ref_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5556_: u8 = 0;
    let mut v_isSharedCheck_5557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5486_ =
                    l_Lean_Server_Test_Cancel_tacticBlock__until__cancelled___00__closed__1;
                crate::leanh::lean_inc(v_x_5476_);
                v___x_5487_ = l_Lean_Syntax_isOfKind(v_x_5476_, v___x_5486_);
                if v___x_5487_ == 0 {
                    crate::leanh::lean_dec(v_x_5476_);
                    v___x_5488_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__0___redArg();
                    return v___x_5488_;
                } else {
                    v___x_5489_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_label_5490_ = l_Lean_Syntax_getArg(v_x_5476_, v___x_5489_);
                    crate::leanh::lean_dec(v_x_5476_);
                    v_lbl_5491_ = l_Lean_TSyntax_getString(v_label_5490_);
                    crate::leanh::lean_dec(v_label_5490_);
                    crate::leanh::lean_inc_ref(v_lbl_5491_);
                    v___x_5492_ = l_Lean_Server_Test_Cancel_mkTestTask(v_lbl_5491_);
                    if crate::leanh::lean_obj_tag(v___x_5492_) == 0 {
                        v___x_5493_ = l_Lean_Server_Test_Cancel_testTasksRef;
                        v___x_5494_ = lean_st_ref_get(v___x_5493_);
                        v___x_5495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__test__task____1_spec__0___redArg(v___x_5494_, v_lbl_5491_);
                        crate::leanh::lean_dec_ref(v_lbl_5491_);
                        crate::leanh::lean_dec(v___x_5494_);
                        if crate::leanh::lean_obj_tag(v___x_5495_) == 1 {
                            v_val_5496_ = crate::leanh::lean_ctor_get(v___x_5495_, 0);
                            v_isSharedCheck_5505_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5495_)) as u8;
                            if v_isSharedCheck_5505_ == 0 {
                                v___x_5498_ = v___x_5495_;
                                v_isShared_5499_ = v_isSharedCheck_5505_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_5496_);
                                crate::leanh::lean_dec(v___x_5495_);
                                v___x_5498_ = crate::leanh::lean_box(0);
                                v_isShared_5499_ = v_isSharedCheck_5505_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_5495_);
                            v___x_5506_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1), core::ptr::addr_of_mut!(l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1_once), _init_l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__1);
                            v___x_5507_ = l_panic___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__5(v___x_5506_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_, v_a_5484_);
                            return v___x_5507_;
                        }
                    } else {
                        v_val_5508_ = crate::leanh::lean_ctor_get(v___x_5492_, 0);
                        v_isSharedCheck_5557_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5492_)) as u8;
                        if v_isSharedCheck_5557_ == 0 {
                            v___x_5510_ = v___x_5492_;
                            v_isShared_5511_ = v_isSharedCheck_5557_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5508_);
                            crate::leanh::lean_dec(v___x_5492_);
                            v___x_5510_ = crate::leanh::lean_box(0);
                            v_isShared_5511_ = v_isSharedCheck_5557_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5500_ = lean_io_wait(v_val_5496_);
                crate::leanh::lean_dec(v___x_5500_);
                v___x_5501_ = crate::leanh::lean_box(0);
                if v_isShared_5499_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5498_, 0);
                    crate::leanh::lean_ctor_set(v___x_5498_, 0, v___x_5501_);
                    v___x_5503_ = v___x_5498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5504_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5501_);
                    v___x_5503_ = v_reuseFailAlloc_5504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5503_;
            }
            3 => {
                v___x_5512_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___closed__2;
                crate::leanh::lean_inc_ref(v_lbl_5491_);
                v___x_5513_ = lean_string_append(v_lbl_5491_, v___x_5512_);
                v___x_5514_ = l_IO_eprintln___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticWait__for__cancel__once__1_spec__3(v___x_5513_);
                if crate::leanh::lean_obj_tag(v___x_5514_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5514_, 1);
                    v___x_5515_ = l_Lean_Server_Test_Cancel_resolveSyncPromise(v_lbl_5491_);
                    v___x_5516_ = crate::leanh::lean_box(0);
                    v___x_5531_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v_a_5483_);
                    if crate::leanh::lean_obj_tag(v___x_5531_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5531_, 1);
                        v_a_5518_ = v___x_5516_;
                        state = 4;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_5531_) == 0 {
                            v_a_5532_ = crate::leanh::lean_ctor_get(v___x_5531_, 0);
                            crate::leanh::lean_inc(v_a_5532_);
                            crate::leanh::lean_dec_ref_known(v___x_5531_, 1);
                            v_a_5518_ = v_a_5532_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_5510_);
                            v_a_5533_ = crate::leanh::lean_ctor_get(v___x_5531_, 0);
                            crate::leanh::lean_inc(v_a_5533_);
                            crate::leanh::lean_dec_ref_known(v___x_5531_, 1);
                            v___x_5534_ = crate::leanh::lean_box(0);
                            v___x_5535_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_5516_, v_val_5508_, v___x_5534_);
                            crate::leanh::lean_dec(v_val_5508_);
                            v_isSharedCheck_5542_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5535_)) as u8;
                            if v_isSharedCheck_5542_ == 0 {
                                v_unused_5543_ = crate::leanh::lean_ctor_get(v___x_5535_, 0);
                                crate::leanh::lean_dec(v_unused_5543_);
                                v___x_5537_ = v___x_5535_;
                                v_isShared_5538_ = v_isSharedCheck_5542_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5535_);
                                v___x_5537_ = crate::leanh::lean_box(0);
                                v_isShared_5538_ = v_isSharedCheck_5542_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5510_);
                    crate::leanh::lean_dec(v_val_5508_);
                    crate::leanh::lean_dec_ref(v_lbl_5491_);
                    v_a_5544_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                    v_isSharedCheck_5556_ = (!crate::leanh::lean_is_exclusive(v___x_5514_)) as u8;
                    if v_isSharedCheck_5556_ == 0 {
                        v___x_5546_ = v___x_5514_;
                        v_isShared_5547_ = v_isSharedCheck_5556_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5544_);
                        crate::leanh::lean_dec(v___x_5514_);
                        v___x_5546_ = crate::leanh::lean_box(0);
                        v_isShared_5547_ = v_isSharedCheck_5556_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5510_, 0, v_a_5518_);
                    v___x_5520_ = v___x_5510_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5518_);
                    v___x_5520_ = v_reuseFailAlloc_5530_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5521_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___lam__0(v___x_5516_, v_val_5508_, v___x_5520_);
                crate::leanh::lean_dec_ref(v___x_5520_);
                crate::leanh::lean_dec(v_val_5508_);
                v_isSharedCheck_5528_ = (!crate::leanh::lean_is_exclusive(v___x_5521_)) as u8;
                if v_isSharedCheck_5528_ == 0 {
                    v_unused_5529_ = crate::leanh::lean_ctor_get(v___x_5521_, 0);
                    crate::leanh::lean_dec(v_unused_5529_);
                    v___x_5523_ = v___x_5521_;
                    v_isShared_5524_ = v_isSharedCheck_5528_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5521_);
                    v___x_5523_ = crate::leanh::lean_box(0);
                    v_isShared_5524_ = v_isSharedCheck_5528_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5523_, 0, v_a_5518_);
                    v___x_5526_ = v___x_5523_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5518_);
                    v___x_5526_ = v_reuseFailAlloc_5527_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5526_;
            }
            8 => {
                if v_isShared_5538_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5537_, 1);
                    crate::leanh::lean_ctor_set(v___x_5537_, 0, v_a_5533_);
                    v___x_5540_ = v___x_5537_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_a_5533_);
                    v___x_5540_ = v_reuseFailAlloc_5541_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5540_;
            }
            10 => {
                v_ref_5548_ = crate::leanh::lean_ctor_get(v_a_5483_, 5);
                v___x_5549_ = lean_io_error_to_string(v_a_5544_);
                v___x_5550_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5550_, 0, v___x_5549_);
                v___x_5551_ = l_Lean_MessageData_ofFormat(v___x_5550_);
                crate::leanh::lean_inc(v_ref_5548_);
                v___x_5552_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5552_, 0, v_ref_5548_);
                crate::leanh::lean_ctor_set(v___x_5552_, 1, v___x_5551_);
                if v_isShared_5547_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5546_, 0, v___x_5552_);
                    v___x_5554_ = v___x_5546_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5555_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5552_);
                    v___x_5554_ = v_reuseFailAlloc_5555_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1___boxed(
    mut v_x_5558_: *mut crate::leanh::LeanObject,
    mut v_a_5559_: *mut crate::leanh::LeanObject,
    mut v_a_5560_: *mut crate::leanh::LeanObject,
    mut v_a_5561_: *mut crate::leanh::LeanObject,
    mut v_a_5562_: *mut crate::leanh::LeanObject,
    mut v_a_5563_: *mut crate::leanh::LeanObject,
    mut v_a_5564_: *mut crate::leanh::LeanObject,
    mut v_a_5565_: *mut crate::leanh::LeanObject,
    mut v_a_5566_: *mut crate::leanh::LeanObject,
    mut v_a_5567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5568_ = l_Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1(v_x_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_);
    crate::leanh::lean_dec(v_a_5566_);
    crate::leanh::lean_dec_ref(v_a_5565_);
    crate::leanh::lean_dec(v_a_5564_);
    crate::leanh::lean_dec_ref(v_a_5563_);
    crate::leanh::lean_dec(v_a_5562_);
    crate::leanh::lean_dec_ref(v_a_5561_);
    crate::leanh::lean_dec(v_a_5560_);
    crate::leanh::lean_dec_ref(v_a_5559_);
    return v_res_5568_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0(
    mut v_inst_5569_: *mut crate::leanh::LeanObject,
    mut v_a_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
    mut v___y_5572_: *mut crate::leanh::LeanObject,
    mut v___y_5573_: *mut crate::leanh::LeanObject,
    mut v___y_5574_: *mut crate::leanh::LeanObject,
    mut v___y_5575_: *mut crate::leanh::LeanObject,
    mut v___y_5576_: *mut crate::leanh::LeanObject,
    mut v___y_5577_: *mut crate::leanh::LeanObject,
    mut v___y_5578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5580_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___redArg(v___y_5577_);
    return v___x_5580_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0___boxed(
    mut v_inst_5581_: *mut crate::leanh::LeanObject,
    mut v_a_5582_: *mut crate::leanh::LeanObject,
    mut v___y_5583_: *mut crate::leanh::LeanObject,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
    mut v___y_5585_: *mut crate::leanh::LeanObject,
    mut v___y_5586_: *mut crate::leanh::LeanObject,
    mut v___y_5587_: *mut crate::leanh::LeanObject,
    mut v___y_5588_: *mut crate::leanh::LeanObject,
    mut v___y_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5592_ = l___private_Init_While_0__whileM_erased___at___00Lean_Server_Test_Cancel___aux__Lean__Server__Test__Cancel______elabRules__Lean__Server__Test__Cancel__tacticBlock__until__cancelled____1_spec__0(v_inst_5581_, v_a_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_);
    crate::leanh::lean_dec(v___y_5590_);
    crate::leanh::lean_dec_ref(v___y_5589_);
    crate::leanh::lean_dec(v___y_5588_);
    crate::leanh::lean_dec_ref(v___y_5587_);
    crate::leanh::lean_dec(v___y_5586_);
    crate::leanh::lean_dec_ref(v___y_5585_);
    crate::leanh::lean_dec(v___y_5584_);
    crate::leanh::lean_dec_ref(v___y_5583_);
    return v_res_5592_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Test_Cancel(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Test_Cancel(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_3167384629____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_Test_Cancel_onceRef = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Server_Test_Cancel_onceRef);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_2861725383____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_Test_Cancel_unblockedCancelTkRef = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Server_Test_Cancel_unblockedCancelTkRef);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_4281145543____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_Test_Cancel_cmdOnceRef = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Server_Test_Cancel_cmdOnceRef);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_651650561____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_Test_Cancel_testTasksRef = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Server_Test_Cancel_testTasksRef);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_Test_Cancel_0__Lean_Server_Test_Cancel_initFn_00___x40_Lean_Server_Test_Cancel_1277954624____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Server_Test_Cancel_syncPromisesRef = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Server_Test_Cancel_syncPromisesRef);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Test_Cancel(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Test_Cancel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Test_Cancel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Test_Cancel(builtin);
}

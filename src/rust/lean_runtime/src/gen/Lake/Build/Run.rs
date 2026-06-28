// Lean compiler output
// Module: Lake.Build.Run
// Imports: Lake.Config.Workspace Lake.Config.Monad Lake.Build.Job.Monad Lake.Build.Index Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Fin::Basic::l_Fin_add;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_versionStringCore;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqBool___boxed,
    l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::System::IO::{l_IO_sleep, l_instMonadBaseIO};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Build::Context::l_Lake_BuildConfig_showProgress;
use crate::r#gen::Lake::Build::Index::{
    initialize_Lake_Build_Index, l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed,
    runtime_initialize_Lake_Build_Index,
};
use crate::r#gen::Lake::Build::Job::Basic::{
    l_Lake_Job_toOpaque___redArg, l_Lake_JobAction_verb, l_Lake_instOrdJobAction_ord,
};
use crate::r#gen::Lake::Build::Job::Monad::{
    initialize_Lake_Build_Job_Monad, l_Lake_Job_async___redArg,
    runtime_initialize_Lake_Build_Job_Monad,
};
use crate::r#gen::Lake::Build::Trace::l_Lake_Hash_nil;
use crate::r#gen::Lake::Config::Cache::l_Lake_CacheMap_writeFile;
use crate::r#gen::Lake::Config::Env::l_Lake_Env_leanGithash;
use crate::r#gen::Lake::Config::Monad::{
    initialize_Lake_Config_Monad, runtime_initialize_Lake_Config_Monad,
};
use crate::r#gen::Lake::Config::Workspace::{
    initialize_Lake_Config_Workspace, l_Lake_Workspace_isRootArtifactCacheWritable,
    runtime_initialize_Lake_Config_Workspace,
};
use crate::r#gen::Lake::Util::Log::{
    l_Lake_Ansi_chalk, l_Lake_AnsiMode_isEnabled, l_Lake_Log_maxLv, l_Lake_LogLevel_ansiColor,
    l_Lake_LogLevel_icon, l_Lake_OutStream_get, l_Lake_instDecidableEqVerbosity,
    l_Lake_instOrdLogLevel_ord, l_Lake_logToStream,
};
use crate::lean_imports_rs::Init::Core::{lean_strict_and, lean_task_get_own};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget_borrowed, lean_mk_array};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint32_of_nat, lean_uint32_to_uint8, lean_usize_add, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_hash, lean_string_utf8_byte_size, lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_exit, lean_io_get_task_state, lean_io_mono_ms_now, lean_io_wait,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lake_mkBuildContext___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_mkBuildContext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkBuildContext___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_mkBuildContext___closed__1_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [76, 101, 97, 110, 32, 0],
    };
static mut l_Lake_mkBuildContext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkBuildContext___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_mkBuildContext___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_mkBuildContext___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_mkBuildContext___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [44, 32, 99, 111, 109, 109, 105, 116, 32, 0],
    };
static mut l_Lake_mkBuildContext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkBuildContext___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_mkBuildContext___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_mkBuildContext___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_mkBuildContext___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_mkBuildContext___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_mkBuildContext___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_mkBuildContext___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [27, 91, 50, 75, 13, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_Build_Run_0__Lake_Ansi_resetLine: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_value:
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
        76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 46, 82, 117, 110, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__2_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 46,
        82, 117, 110, 46, 48, 46, 76, 97, 107, 101, 46, 112, 114, 105, 110, 116, 33, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__3_value:
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
    m_data: [91, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value:
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
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11079354408986465895 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value:
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
    m_data: [76, 97, 107, 101, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value:
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
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value)
            as *mut crate::leanh::LeanObject,
        12997130533650095963 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [66, 117, 105, 108, 100, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value:
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
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__8_value)
            as *mut crate::leanh::LeanObject,
        10213429595551467778 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value:
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
    m_data: [82, 117, 110, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value:
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
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__10_value)
            as *mut crate::leanh::LeanObject,
        3222535058389389878 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__11_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        16005566182676762847 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value:
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
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__12_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__6_value)
            as *mut crate::leanh::LeanObject,
        8167123355711996387 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value:
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
    m_data: [112, 114, 105, 110, 116, 33, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value:
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
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__14_value)
            as *mut crate::leanh::LeanObject,
        11754600101891422379 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__18_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [32, 102, 97, 105, 108, 101, 100, 58, 32, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_value:
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
    m_data: [93, 32, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_print_x21___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1_value:
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
static mut l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2_value:
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
    m_data: [32, 91, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3_value:
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
    m_data: [47, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [82, 117, 110, 110, 105, 110, 103, 32, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5_value:
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
    m_data: [32, 40, 43, 32, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6_value:
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
    m_data: [32, 109, 111, 114, 101, 41, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0_value:
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
    m_data: [109, 115, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1_value:
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
    m_data: [46, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2_value:
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
    m_data: [115, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0_value:
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
    m_data: [10, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1_value:
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
    m_data: [93, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2_value:
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
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3_value:
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
    m_data: [51, 50, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4_value:
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
    m_data: [32, 40, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5_value:
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
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6_value:
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
    m_data: [32, 40, 79, 112, 116, 105, 111, 110, 97, 108, 41, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0_value:
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
        core::ptr::addr_of!(l_Lake_mkBuildContext___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_mkBuildContext___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_noBuildCode: u32 = 0;
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_value:
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
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_value:
    crate::leanh::LeanStringObject<67> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 67,
    m_capacity: 67,
    m_length: 66,
    m_data: [
        84, 104, 101, 114, 101, 32, 119, 101, 114, 101, 32, 105, 115, 115, 117, 101, 115, 32, 115,
        97, 118, 105, 110, 103, 32, 105, 110, 112, 117, 116, 45, 116, 111, 45, 111, 117, 116, 112,
        117, 116, 32, 109, 97, 112, 112, 105, 110, 103, 115, 32, 102, 114, 111, 109, 32, 116, 104,
        101, 32, 98, 117, 105, 108, 100, 58, 10, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_value:
    crate::leanh::LeanStringObject<57> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 97, 118, 101, 32, 105, 110, 112, 117,
        116, 45, 116, 111, 45, 111, 117, 116, 112, 117, 116, 32, 109, 97, 112, 112, 105, 110, 103,
        115, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 98, 117, 105, 108, 100, 46, 10, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_value:
    crate::leanh::LeanStringObject<88> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 88,
    m_capacity: 88,
    m_length: 87,
    m_data: [
        87, 111, 114, 107, 115, 112, 97, 99, 101, 32, 109, 105, 115, 115, 105, 110, 103, 32, 105,
        110, 112, 117, 116, 45, 116, 111, 45, 111, 117, 116, 112, 117, 116, 32, 109, 97, 112, 112,
        105, 110, 103, 115, 32, 102, 114, 111, 109, 32, 98, 117, 105, 108, 100, 46, 32, 40, 84,
        104, 105, 115, 32, 105, 115, 32, 108, 105, 107, 101, 108, 121, 32, 97, 32, 98, 117, 103,
        32, 105, 110, 32, 76, 97, 107, 101, 46, 41, 10, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_value:
    crate::leanh::LeanStringObject<162> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 162,
    m_capacity: 162,
    m_length: 161,
    m_data: [
        58, 32, 116, 104, 101, 32, 97, 114, 116, 105, 102, 97, 99, 116, 32, 99, 97, 99, 104, 101,
        32, 105, 115, 32, 110, 111, 116, 32, 101, 110, 97, 98, 108, 101, 100, 32, 102, 111, 114,
        32, 116, 104, 105, 115, 32, 112, 97, 99, 107, 97, 103, 101, 44, 32, 115, 111, 32, 116, 104,
        101, 32, 97, 114, 116, 105, 102, 97, 99, 116, 115, 32, 100, 101, 115, 99, 114, 105, 98,
        101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 109, 97, 112, 112, 105, 110, 103, 115, 32,
        112, 114, 111, 100, 117, 99, 101, 100, 32, 98, 121, 32, 96, 45, 111, 96, 32, 119, 105, 108,
        108, 32, 110, 111, 116, 32, 110, 101, 99, 101, 115, 115, 97, 114, 105, 108, 121, 32, 98,
        101, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 105, 110, 32, 116, 104, 101, 32, 99,
        97, 99, 104, 101, 46, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_reportResult___closed__0_value:
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
        66, 117, 105, 108, 100, 32, 99, 111, 109, 112, 108, 101, 116, 101, 100, 32, 115, 117, 99,
        99, 101, 115, 115, 102, 117, 108, 108, 121, 32, 40, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_reportResult___closed__1_value:
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
    m_data: [41, 46, 10, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_reportResult___closed__2_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        65, 108, 108, 32, 116, 97, 114, 103, 101, 116, 115, 32, 117, 112, 45, 116, 111, 45, 100,
        97, 116, 101, 32, 40, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_reportResult___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 106, 111, 98, 115, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_reportResult___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [49, 32, 106, 111, 98, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_reportResult___closed__5_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
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
        78, 111, 116, 104, 105, 110, 103, 32, 116, 111, 32, 98, 117, 105, 108, 100, 46, 10, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_reportResult___closed__9_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        83, 111, 109, 101, 32, 114, 101, 113, 117, 105, 114, 101, 100, 32, 116, 97, 114, 103, 101,
        116, 115, 32, 108, 111, 103, 103, 101, 100, 32, 102, 97, 105, 108, 117, 114, 101, 115, 58,
        10, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_reportResult___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0_value:
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
static mut l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [98, 117, 105, 108, 100, 32, 102, 97, 105, 108, 101, 100, 0],
};
static mut l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2_value:
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
        l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3_value:
    crate::leanh::LeanStringObject<64> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 64,
    m_capacity: 64,
    m_length: 63,
    m_data: [
        117, 110, 99, 97, 117, 103, 104, 116, 32, 116, 111, 112, 45, 108, 101, 118, 101, 108, 32,
        98, 117, 105, 108, 100, 32, 102, 97, 105, 108, 117, 114, 101, 32, 40, 116, 104, 105, 115,
        32, 105, 115, 32, 108, 105, 107, 101, 108, 121, 32, 97, 32, 98, 117, 103, 32, 105, 110, 32,
        76, 97, 107, 101, 41, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4_value:
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
        l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0_value:
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
static mut l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value:
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
    m_fun: l___private_Lake_Build_Index_0__Lake_recFetchWithIndex___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0: u8 = 0;
pub static l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__0_value:
    crate::leanh::LeanStringObject<76> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 76,
    m_capacity: 76,
    m_length: 75,
    m_data: [
        117, 110, 99, 97, 117, 103, 104, 116, 32, 116, 111, 112, 45, 108, 101, 118, 101, 108, 32,
        98, 117, 105, 108, 100, 32, 102, 97, 105, 108, 117, 114, 101, 32, 40, 116, 104, 105, 115,
        32, 105, 115, 32, 108, 105, 107, 101, 108, 121, 32, 97, 32, 98, 117, 103, 32, 105, 110, 32,
        116, 104, 101, 32, 98, 117, 105, 108, 100, 32, 115, 99, 114, 105, 112, 116, 41, 0,
    ],
};
static mut l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1_value:
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
        l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Workspace_checkNoBuild___redArg___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        259 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_Workspace_checkNoBuild___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_checkNoBuild___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Workspace_checkNoBuild___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    4,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Workspace_checkNoBuild___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        16843008 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_Workspace_checkNoBuild___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_checkNoBuild___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Workspace_checkNoBuild___redArg___closed__2_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        106, 111, 98, 32, 99, 111, 109, 112, 117, 116, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lake_Workspace_checkNoBuild___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_checkNoBuild___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake_mkBuildContext___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2323_ = l_Lean_versionStringCore;
    v___x_2324_ = l_Lake_mkBuildContext___closed__1;
    v___x_2325_ = lean_string_append(v___x_2324_, v___x_2323_);
    return v___x_2325_;
}
pub unsafe fn _init_l_Lake_mkBuildContext___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_Lake_mkBuildContext___closed__3;
    v___x_2328_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__2),
        core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__2_once),
        _init_l_Lake_mkBuildContext___closed__2,
    );
    v___x_2329_ = lean_string_append(v___x_2328_, v___x_2327_);
    return v___x_2329_;
}
pub unsafe fn _init_l_Lake_mkBuildContext___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2330_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2331_ = lean_nat_to_int(v___x_2330_);
    return v___x_2331_;
}
pub unsafe fn _init_l_Lake_mkBuildContext___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_2332_: u32 = 0;
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2332_ = 0;
    v___x_2333_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__5),
        core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__5_once),
        _init_l_Lake_mkBuildContext___closed__5,
    );
    v___x_2334_ = crate::leanh::lean_alloc_ctor(0, 1, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_2334_, 0, v___x_2333_);
    crate::leanh::lean_ctor_set_uint32(
        v___x_2334_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2332_,
    );
    return v___x_2334_;
}
pub unsafe fn l_Lake_mkBuildContext(
    mut v_ws_2335_: *mut crate::leanh::LeanObject,
    mut v_config_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: u64 = 0;
    let mut v___x_2343_: u64 = 0;
    let mut v___x_2344_: u64 = 0;
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Lake_mkBuildContext___closed__0;
    v___x_2339_ = lean_st_mk_ref(v___x_2338_);
    v_lakeEnv_2340_ = crate::leanh::lean_ctor_get(v_ws_2335_, 0);
    v___x_2341_ = l_Lake_Env_leanGithash(v_lakeEnv_2340_);
    v___x_2342_ = l_Lake_Hash_nil;
    v___x_2343_ = lean_string_hash(v___x_2341_);
    v___x_2344_ = lean_uint64_mix_hash(v___x_2342_, v___x_2343_);
    v___x_2345_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__4),
        core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__4_once),
        _init_l_Lake_mkBuildContext___closed__4,
    );
    v___x_2346_ = lean_string_append(v___x_2345_, v___x_2341_);
    crate::leanh::lean_dec_ref(v___x_2341_);
    v___x_2347_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__6),
        core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__6_once),
        _init_l_Lake_mkBuildContext___closed__6,
    );
    v___x_2348_ = crate::leanh::lean_alloc_ctor(0, 3, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_2348_, 0, v___x_2346_);
    crate::leanh::lean_ctor_set(v___x_2348_, 1, v___x_2338_);
    crate::leanh::lean_ctor_set(v___x_2348_, 2, v___x_2347_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_2348_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_2344_,
    );
    v___x_2349_ = crate::leanh::lean_box(0);
    v___x_2350_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2350_, 0, v_config_2336_);
    crate::leanh::lean_ctor_set(v___x_2350_, 1, v_ws_2335_);
    crate::leanh::lean_ctor_set(v___x_2350_, 2, v___x_2348_);
    crate::leanh::lean_ctor_set(v___x_2350_, 3, v___x_2339_);
    crate::leanh::lean_ctor_set(v___x_2350_, 4, v___x_2349_);
    return v___x_2350_;
}
pub unsafe fn l_Lake_mkBuildContext___boxed(
    mut v_ws_2351_: *mut crate::leanh::LeanObject,
    mut v_config_2352_: *mut crate::leanh::LeanObject,
    mut v_a_2353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2354_ = l_Lake_mkBuildContext(v_ws_2351_, v_config_2352_);
    return v_res_2354_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2355_: u32 = 0;
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = 10493;
    v___x_2356_ = crate::leanh::lean_box_uint32(v___x_2355_);
    return v___x_2356_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2357_: u32 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2357_ = 10491;
    v___x_2358_ = crate::leanh::lean_box_uint32(v___x_2357_);
    return v___x_2358_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2359_: u32 = 0;
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2359_ = 10431;
    v___x_2360_ = crate::leanh::lean_box_uint32(v___x_2359_);
    return v___x_2360_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2361_: u32 = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2361_ = 10367;
    v___x_2362_ = crate::leanh::lean_box_uint32(v___x_2361_);
    return v___x_2362_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2363_: u32 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2363_ = 10463;
    v___x_2364_ = crate::leanh::lean_box_uint32(v___x_2363_);
    return v___x_2364_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2365_: u32 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2365_ = 10479;
    v___x_2366_ = crate::leanh::lean_box_uint32(v___x_2365_);
    return v___x_2366_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2367_: u32 = 0;
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2367_ = 10487;
    v___x_2368_ = crate::leanh::lean_box_uint32(v___x_2367_);
    return v___x_2368_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2369_: u32 = 0;
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = 10494;
    v___x_2370_ = crate::leanh::lean_box_uint32(v___x_2369_);
    return v___x_2370_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_2372_ = lean_mk_empty_array_with_capacity(v___x_2371_);
    v___x_2373_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8;
    v___x_2374_ = lean_array_push(v___x_2372_, v___x_2373_);
    v___x_2375_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7;
    v___x_2376_ = lean_array_push(v___x_2374_, v___x_2375_);
    v___x_2377_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6;
    v___x_2378_ = lean_array_push(v___x_2376_, v___x_2377_);
    v___x_2379_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5;
    v___x_2380_ = lean_array_push(v___x_2378_, v___x_2379_);
    v___x_2381_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4;
    v___x_2382_ = lean_array_push(v___x_2380_, v___x_2381_);
    v___x_2383_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3;
    v___x_2384_ = lean_array_push(v___x_2382_, v___x_2383_);
    v___x_2385_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2;
    v___x_2386_ = lean_array_push(v___x_2384_, v___x_2385_);
    v___x_2387_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1;
    v___x_2388_ = lean_array_push(v___x_2386_, v___x_2387_);
    return v___x_2388_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2389_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0_once
        ),
        _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0,
    );
    return v___x_2389_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(
    mut v_out_2390_: *mut crate::leanh::LeanObject,
    mut v_outLv_2391_: u8,
    mut v_useAnsi_2392_: u8,
    mut v_e_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = l_Lake_logToStream(v_e_2393_, v_out_2390_, v_outLv_2391_, v_useAnsi_2392_);
    return v___x_2395_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed(
    mut v_out_2396_: *mut crate::leanh::LeanObject,
    mut v_outLv_2397_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_2398_: *mut crate::leanh::LeanObject,
    mut v_e_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_outLv_boxed_2401_: u8 = 0;
    let mut v_useAnsi_boxed_2402_: u8 = 0;
    let mut v_res_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_outLv_boxed_2401_ = (crate::leanh::lean_unbox(v_outLv_2397_) as u8);
    v_useAnsi_boxed_2402_ = (crate::leanh::lean_unbox(v_useAnsi_2398_) as u8);
    v_res_2403_ = l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0(
        v_out_2396_,
        v_outLv_boxed_2401_,
        v_useAnsi_boxed_2402_,
        v_e_2399_,
    );
    crate::leanh::lean_dec_ref(v_e_2399_);
    return v_res_2403_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_MonitorContext_logger(
    mut v_ctx_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_out_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_outLv_2406_: u8 = 0;
    let mut v_useAnsi_2407_: u8 = 0;
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_out_2405_ = crate::leanh::lean_ctor_get(v_ctx_2404_, 1);
    crate::leanh::lean_inc_ref(v_out_2405_);
    v_outLv_2406_ = crate::leanh::lean_ctor_get_uint8(
        v_ctx_2404_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v_useAnsi_2407_ = crate::leanh::lean_ctor_get_uint8(
        v_ctx_2404_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
    );
    crate::leanh::lean_dec_ref(v_ctx_2404_);
    v___x_2408_ = crate::leanh::lean_box((v_outLv_2406_) as usize);
    v___x_2409_ = crate::leanh::lean_box((v_useAnsi_2407_) as usize);
    v___f_2410_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Build_Run_0__Lake_MonitorContext_logger___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2410_, 0, v_out_2405_);
    crate::leanh::lean_closure_set(v___f_2410_, 1, v___x_2408_);
    crate::leanh::lean_closure_set(v___f_2410_, 2, v___x_2409_);
    return v___f_2410_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(
    mut v_ctx_2411_: *mut crate::leanh::LeanObject,
    mut v_s_2412_: *mut crate::leanh::LeanObject,
    mut v_self_2413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2415_ = crate::leanh::lean_apply_3(
        v_self_2413_,
        v_ctx_2411_,
        v_s_2412_,
        crate::leanh::lean_box(0),
    );
    return v___x_2415_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg___boxed(
    mut v_ctx_2416_: *mut crate::leanh::LeanObject,
    mut v_s_2417_: *mut crate::leanh::LeanObject,
    mut v_self_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2420_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run___redArg(
        v_ctx_2416_,
        v_s_2417_,
        v_self_2418_,
    );
    return v_res_2420_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_MonitorM_run(
    mut v_00_u03b1_2421_: *mut crate::leanh::LeanObject,
    mut v_ctx_2422_: *mut crate::leanh::LeanObject,
    mut v_s_2423_: *mut crate::leanh::LeanObject,
    mut v_self_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = crate::leanh::lean_apply_3(
        v_self_2424_,
        v_ctx_2422_,
        v_s_2423_,
        crate::leanh::lean_box(0),
    );
    return v___x_2426_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_MonitorM_run___boxed(
    mut v_00_u03b1_2427_: *mut crate::leanh::LeanObject,
    mut v_ctx_2428_: *mut crate::leanh::LeanObject,
    mut v_s_2429_: *mut crate::leanh::LeanObject,
    mut v_self_2430_: *mut crate::leanh::LeanObject,
    mut v_a_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2432_ = l___private_Lake_Build_Run_0__Lake_MonitorM_run(
        v_00_u03b1_2427_,
        v_ctx_2428_,
        v_s_2429_,
        v_self_2430_,
    );
    return v_res_2432_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_flush(
    mut v_out_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flush_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flush_2437_ = crate::leanh::lean_ctor_get(v_out_2435_, 0);
    crate::leanh::lean_inc_ref(v_flush_2437_);
    crate::leanh::lean_dec_ref(v_out_2435_);
    v___x_2438_ = crate::leanh::lean_apply_1(v_flush_2437_, crate::leanh::lean_box(0));
    if crate::leanh::lean_obj_tag(v___x_2438_) == 0 {
        let mut v_a_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2439_ = crate::leanh::lean_ctor_get(v___x_2438_, 0);
        crate::leanh::lean_inc(v_a_2439_);
        crate::leanh::lean_dec_ref_known(v___x_2438_, 1);
        return v_a_2439_;
    } else {
        let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_2438_, 1);
        v___x_2440_ = crate::leanh::lean_box(0);
        return v___x_2440_;
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_flush___boxed(
    mut v_out_2441_: *mut crate::leanh::LeanObject,
    mut v_a_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2443_ = l___private_Lake_Build_Run_0__Lake_flush(v_out_2441_);
    return v_res_2443_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ = crate::leanh::lean_box(0);
    v___x_2445_ = l_instMonadBaseIO;
    v___x_2446_ = l_instInhabitedOfMonad___redArg(v___x_2445_, v___x_2444_);
    return v___x_2446_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2476_: u8 = 0;
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = 1;
    v___x_2477_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
    v___x_2478_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2477_, v___x_2476_);
    return v___x_2478_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16),
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__16_once),
        _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__16,
    );
    v___x_2480_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
    v___x_2481_ = lean_string_append(v___x_2480_, v___x_2479_);
    return v___x_2481_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2483_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
    v___x_2484_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__17),
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__17_once),
        _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__17,
    );
    v___x_2485_ = lean_string_append(v___x_2484_, v___x_2483_);
    return v___x_2485_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_print_x21(
    mut v_out_2487_: *mut crate::leanh::LeanObject,
    mut v_s_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_putStr_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2496_: u8 = 0;
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181__overap_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_putStr_2490_ = crate::leanh::lean_ctor_get(v_out_2487_, 4);
                crate::leanh::lean_inc_ref(v_putStr_2490_);
                crate::leanh::lean_dec_ref(v_out_2487_);
                crate::leanh::lean_inc_ref(v_s_2488_);
                v___x_2491_ = crate::leanh::lean_apply_2(
                    v_putStr_2490_,
                    v_s_2488_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2491_) == 0 {
                    crate::leanh::lean_dec_ref(v_s_2488_);
                    v_a_2492_ = crate::leanh::lean_ctor_get(v___x_2491_, 0);
                    crate::leanh::lean_inc(v_a_2492_);
                    crate::leanh::lean_dec_ref_known(v___x_2491_, 1);
                    return v_a_2492_;
                } else {
                    v_a_2493_ = crate::leanh::lean_ctor_get(v___x_2491_, 0);
                    v_isSharedCheck_2518_ = (!crate::leanh::lean_is_exclusive(v___x_2491_)) as u8;
                    if v_isSharedCheck_2518_ == 0 {
                        v___x_2495_ = v___x_2491_;
                        v_isShared_2496_ = v_isSharedCheck_2518_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2493_);
                        crate::leanh::lean_dec(v___x_2491_);
                        v___x_2495_ = crate::leanh::lean_box(0);
                        v_isShared_2496_ = v_isSharedCheck_2518_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2497_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once
                    ),
                    _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0,
                );
                v___x_2498_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                v___x_2499_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                v___x_2500_ = crate::leanh::lean_unsigned_to_nat(89);
                v___x_2501_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2502_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2503_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once
                    ),
                    _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19,
                );
                v___x_2504_ = lean_io_error_to_string(v_a_2493_);
                v___x_2505_ = lean_string_append(v___x_2503_, v___x_2504_);
                crate::leanh::lean_dec_ref(v___x_2504_);
                v___x_2506_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                v___x_2507_ = lean_string_append(v___x_2505_, v___x_2506_);
                v___x_2508_ = l_String_quote(v_s_2488_);
                if v_isShared_2496_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2495_, 3);
                    crate::leanh::lean_ctor_set(v___x_2495_, 0, v___x_2508_);
                    v___x_2510_ = v___x_2495_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2517_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2508_);
                    v___x_2510_ = v_reuseFailAlloc_2517_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2511_ = l_Std_Format_defWidth;
                v___x_2512_ =
                    l_Std_Format_pretty(v___x_2510_, v___x_2511_, v___x_2502_, v___x_2502_);
                v___x_2513_ = lean_string_append(v___x_2507_, v___x_2512_);
                crate::leanh::lean_dec_ref(v___x_2512_);
                v___x_2514_ = l_mkPanicMessageWithDecl(
                    v___x_2498_,
                    v___x_2499_,
                    v___x_2500_,
                    v___x_2501_,
                    v___x_2513_,
                );
                crate::leanh::lean_dec_ref(v___x_2513_);
                v___x_181__overap_2515_ = l_panic___redArg(v___x_2497_, v___x_2514_);
                v___x_2516_ =
                    crate::leanh::lean_apply_1(v___x_181__overap_2515_, crate::leanh::lean_box(0));
                return v___x_2516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_print_x21___boxed(
    mut v_out_2519_: *mut crate::leanh::LeanObject,
    mut v_s_2520_: *mut crate::leanh::LeanObject,
    mut v_a_2521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2522_ = l___private_Lake_Build_Run_0__Lake_print_x21(v_out_2519_, v_s_2520_);
    return v_res_2522_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_print(
    mut v_s_2523_: *mut crate::leanh::LeanObject,
    mut v_a_2524_: *mut crate::leanh::LeanObject,
    mut v_a_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2537_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645__overap_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2530_ = crate::leanh::lean_ctor_get(v_a_2524_, 1);
                v_putStr_2531_ = crate::leanh::lean_ctor_get(v_out_2530_, 4);
                crate::leanh::lean_inc_ref(v_putStr_2531_);
                crate::leanh::lean_inc_ref(v_s_2523_);
                v___x_2532_ = crate::leanh::lean_apply_2(
                    v_putStr_2531_,
                    v_s_2523_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2532_) == 0 {
                    crate::leanh::lean_dec_ref(v_s_2523_);
                    v_a_2533_ = crate::leanh::lean_ctor_get(v___x_2532_, 0);
                    crate::leanh::lean_inc(v_a_2533_);
                    crate::leanh::lean_dec_ref_known(v___x_2532_, 1);
                    v_val_2528_ = v_a_2533_;
                    state = 1;
                    continue;
                } else {
                    v_a_2534_ = crate::leanh::lean_ctor_get(v___x_2532_, 0);
                    v_isSharedCheck_2559_ = (!crate::leanh::lean_is_exclusive(v___x_2532_)) as u8;
                    if v_isSharedCheck_2559_ == 0 {
                        v___x_2536_ = v___x_2532_;
                        v_isShared_2537_ = v_isSharedCheck_2559_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2534_);
                        crate::leanh::lean_dec(v___x_2532_);
                        v___x_2536_ = crate::leanh::lean_box(0);
                        v_isShared_2537_ = v_isSharedCheck_2559_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2529_, 0, v_val_2528_);
                crate::leanh::lean_ctor_set(v___x_2529_, 1, v_a_2525_);
                return v___x_2529_;
            }
            2 => {
                v___x_2538_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once
                    ),
                    _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0,
                );
                v___x_2539_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                v___x_2540_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                v___x_2541_ = crate::leanh::lean_unsigned_to_nat(89);
                v___x_2542_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2543_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2544_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once
                    ),
                    _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19,
                );
                v___x_2545_ = lean_io_error_to_string(v_a_2534_);
                v___x_2546_ = lean_string_append(v___x_2544_, v___x_2545_);
                crate::leanh::lean_dec_ref(v___x_2545_);
                v___x_2547_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                v___x_2548_ = lean_string_append(v___x_2546_, v___x_2547_);
                v___x_2549_ = l_String_quote(v_s_2523_);
                if v_isShared_2537_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2536_, 3);
                    crate::leanh::lean_ctor_set(v___x_2536_, 0, v___x_2549_);
                    v___x_2551_ = v___x_2536_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2549_);
                    v___x_2551_ = v_reuseFailAlloc_2558_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2552_ = l_Std_Format_defWidth;
                v___x_2553_ =
                    l_Std_Format_pretty(v___x_2551_, v___x_2552_, v___x_2543_, v___x_2543_);
                v___x_2554_ = lean_string_append(v___x_2548_, v___x_2553_);
                crate::leanh::lean_dec_ref(v___x_2553_);
                v___x_2555_ = l_mkPanicMessageWithDecl(
                    v___x_2539_,
                    v___x_2540_,
                    v___x_2541_,
                    v___x_2542_,
                    v___x_2554_,
                );
                crate::leanh::lean_dec_ref(v___x_2554_);
                v___x_645__overap_2556_ = l_panic___redArg(v___x_2538_, v___x_2555_);
                v___x_2557_ =
                    crate::leanh::lean_apply_1(v___x_645__overap_2556_, crate::leanh::lean_box(0));
                v_val_2528_ = v___x_2557_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_print___boxed(
    mut v_s_2560_: *mut crate::leanh::LeanObject,
    mut v_a_2561_: *mut crate::leanh::LeanObject,
    mut v_a_2562_: *mut crate::leanh::LeanObject,
    mut v_a_2563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2564_ = l___private_Lake_Build_Run_0__Lake_Monitor_print(v_s_2560_, v_a_2561_, v_a_2562_);
    crate::leanh::lean_dec_ref(v_a_2561_);
    return v_res_2564_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_flush(
    mut v_a_2565_: *mut crate::leanh::LeanObject,
    mut v_a_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_2571_ = crate::leanh::lean_ctor_get(v_a_2565_, 1);
                v_flush_2572_ = crate::leanh::lean_ctor_get(v_out_2571_, 0);
                crate::leanh::lean_inc_ref(v_flush_2572_);
                v___x_2573_ = crate::leanh::lean_apply_1(v_flush_2572_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_2573_) == 0 {
                    v_a_2574_ = crate::leanh::lean_ctor_get(v___x_2573_, 0);
                    crate::leanh::lean_inc(v_a_2574_);
                    crate::leanh::lean_dec_ref_known(v___x_2573_, 1);
                    v_val_2569_ = v_a_2574_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2573_, 1);
                    v___x_2575_ = crate::leanh::lean_box(0);
                    v_val_2569_ = v___x_2575_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2570_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2570_, 0, v_val_2569_);
                crate::leanh::lean_ctor_set(v___x_2570_, 1, v_a_2566_);
                return v___x_2570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_flush___boxed(
    mut v_a_2576_: *mut crate::leanh::LeanObject,
    mut v_a_2577_: *mut crate::leanh::LeanObject,
    mut v_a_2578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2579_ = l___private_Lake_Build_Run_0__Lake_Monitor_flush(v_a_2576_, v_a_2577_);
    crate::leanh::lean_dec_ref(v_a_2576_);
    return v_res_2579_;
}
pub unsafe fn l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(
    mut v_msg_2580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8556__overap_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2582_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__0),
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once),
        _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0,
    );
    v___x_8556__overap_2583_ = lean_panic_fn_borrowed(v___x_2582_, v_msg_2580_);
    v___x_2584_ = crate::leanh::lean_apply_1(v___x_8556__overap_2583_, crate::leanh::lean_box(0));
    return v___x_2584_;
}
pub unsafe fn l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0___boxed(
    mut v_msg_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(
        v_msg_2585_,
    );
    return v_res_2587_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2588_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
    v___x_2589_ = lean_array_get_size(v___x_2588_);
    return v___x_2589_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(
    mut v_running_2596_: *mut crate::leanh::LeanObject,
    mut v_unfinished_2597_: *mut crate::leanh::LeanObject,
    mut v_a_2598_: *mut crate::leanh::LeanObject,
    mut v_a_2599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_showProgress_2604_: u8 = 0;
    let mut v_useAnsi_2605_: u8 = 0;
    let mut v_jobNo_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalJobs_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_2608_: u8 = 0;
    let mut v_failures_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resetCtrl_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUpdate_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spinnerIdx_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2615_: u8 = 0;
    let mut v_out_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: u32 = 0;
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: u8 = 0;
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_showProgress_2604_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2598_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                );
                if v_showProgress_2604_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v_useAnsi_2605_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_2598_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                    );
                    if v_useAnsi_2605_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_jobNo_2606_ = crate::leanh::lean_ctor_get(v_a_2599_, 0);
                        v_totalJobs_2607_ = crate::leanh::lean_ctor_get(v_a_2599_, 1);
                        v_wantsRebuild_2608_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_2599_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        );
                        v_failures_2609_ = crate::leanh::lean_ctor_get(v_a_2599_, 2);
                        v_resetCtrl_2610_ = crate::leanh::lean_ctor_get(v_a_2599_, 3);
                        v_lastUpdate_2611_ = crate::leanh::lean_ctor_get(v_a_2599_, 4);
                        v_spinnerIdx_2612_ = crate::leanh::lean_ctor_get(v_a_2599_, 5);
                        v_isSharedCheck_2701_ = (!crate::leanh::lean_is_exclusive(v_a_2599_)) as u8;
                        if v_isSharedCheck_2701_ == 0 {
                            v___x_2614_ = v_a_2599_;
                            v_isShared_2615_ = v_isSharedCheck_2701_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_spinnerIdx_2612_);
                            crate::leanh::lean_inc(v_lastUpdate_2611_);
                            crate::leanh::lean_inc(v_resetCtrl_2610_);
                            crate::leanh::lean_inc(v_failures_2609_);
                            crate::leanh::lean_inc(v_totalJobs_2607_);
                            crate::leanh::lean_inc(v_jobNo_2606_);
                            crate::leanh::lean_dec(v_a_2599_);
                            v___x_2614_ = crate::leanh::lean_box(0);
                            v_isShared_2615_ = v_isSharedCheck_2701_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2602_ = crate::leanh::lean_box(0);
                v___x_2603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2603_, 0, v___x_2602_);
                crate::leanh::lean_ctor_set(v___x_2603_, 1, v_a_2599_);
                return v___x_2603_;
            }
            2 => {
                v_out_2616_ = crate::leanh::lean_ctor_get(v_a_2598_, 1);
                v___x_2617_ = l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames;
                v___x_2618_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0_once), _init_l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__0);
                v___x_2619_ = lean_array_fget_borrowed(v___x_2617_, v_spinnerIdx_2612_);
                v___x_2620_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2621_ = l_Fin_add(v___x_2618_, v_spinnerIdx_2612_, v___x_2620_);
                crate::leanh::lean_dec(v_spinnerIdx_2612_);
                v___x_2622_ = l___private_Lake_Build_Run_0__Lake_Ansi_resetLine___closed__0;
                crate::leanh::lean_inc(v_totalJobs_2607_);
                crate::leanh::lean_inc(v_jobNo_2606_);
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 5, v___x_2621_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v___x_2622_);
                    v___x_2624_ = v___x_2614_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2700_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_jobNo_2606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_totalJobs_2607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_failures_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 3, v___x_2622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_lastUpdate_2611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 5, v___x_2621_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2700_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        v_wantsRebuild_2608_,
                    );
                    v___x_2624_ = v_reuseFailAlloc_2700_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2680_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2681_ = lean_array_get_size(v_running_2596_);
                v___x_2682_ = lean_nat_dec_lt(v___x_2680_, v___x_2681_);
                if v___x_2682_ == 0 {
                    v___x_2683_ = lean_array_get_size(v_unfinished_2597_);
                    v___x_2684_ = lean_nat_sub(v___x_2683_, v___x_2620_);
                    v___x_2685_ = lean_array_fget_borrowed(v_unfinished_2597_, v___x_2684_);
                    crate::leanh::lean_dec(v___x_2684_);
                    v_caption_2686_ = crate::leanh::lean_ctor_get(v___x_2685_, 2);
                    v___x_2687_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
                    v___x_2688_ = lean_string_append(v___x_2687_, v_caption_2686_);
                    v___y_2634_ = v___x_2688_;
                    state = 6;
                    continue;
                } else {
                    v___x_2689_ = lean_nat_sub(v___x_2681_, v___x_2620_);
                    v___x_2690_ = lean_array_fget_borrowed(v_running_2596_, v___x_2689_);
                    v_caption_2691_ = crate::leanh::lean_ctor_get(v___x_2690_, 2);
                    v___x_2692_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__4;
                    v___x_2693_ = lean_string_append(v___x_2692_, v_caption_2691_);
                    v___x_2694_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__5;
                    v___x_2695_ = lean_string_append(v___x_2693_, v___x_2694_);
                    v___x_2696_ = l_Nat_reprFast(v___x_2689_);
                    v___x_2697_ = lean_string_append(v___x_2695_, v___x_2696_);
                    crate::leanh::lean_dec_ref(v___x_2696_);
                    v___x_2698_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__6;
                    v___x_2699_ = lean_string_append(v___x_2697_, v___x_2698_);
                    v___y_2634_ = v___x_2699_;
                    state = 6;
                    continue;
                }
            }
            4 => {
                v___x_2627_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2627_, 0, v_val_2626_);
                crate::leanh::lean_ctor_set(v___x_2627_, 1, v___x_2624_);
                return v___x_2627_;
            }
            5 => {
                v_flush_2629_ = crate::leanh::lean_ctor_get(v_out_2616_, 0);
                crate::leanh::lean_inc_ref(v_flush_2629_);
                v___x_2630_ = crate::leanh::lean_apply_1(v_flush_2629_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_2630_) == 0 {
                    v_a_2631_ = crate::leanh::lean_ctor_get(v___x_2630_, 0);
                    crate::leanh::lean_inc(v_a_2631_);
                    crate::leanh::lean_dec_ref_known(v___x_2630_, 1);
                    v_val_2626_ = v_a_2631_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2630_, 1);
                    v___x_2632_ = crate::leanh::lean_box(0);
                    v_val_2626_ = v___x_2632_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v_putStr_2635_ = crate::leanh::lean_ctor_get(v_out_2616_, 4);
                v___x_2636_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
                v___x_2637_ = crate::leanh::lean_unbox_uint32(v___x_2619_);
                v___x_2638_ = lean_string_push(v___x_2636_, v___x_2637_);
                v___x_2639_ = lean_string_append(v_resetCtrl_2610_, v___x_2638_);
                crate::leanh::lean_dec_ref(v___x_2638_);
                v___x_2640_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
                v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
                v___x_2642_ = l_Nat_reprFast(v_jobNo_2606_);
                v___x_2643_ = lean_string_append(v___x_2641_, v___x_2642_);
                crate::leanh::lean_dec_ref(v___x_2642_);
                v___x_2644_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
                v___x_2645_ = lean_string_append(v___x_2643_, v___x_2644_);
                v___x_2646_ = l_Nat_reprFast(v_totalJobs_2607_);
                v___x_2647_ = lean_string_append(v___x_2645_, v___x_2646_);
                crate::leanh::lean_dec_ref(v___x_2646_);
                v___x_2648_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                v___x_2649_ = lean_string_append(v___x_2647_, v___x_2648_);
                v___x_2650_ = lean_string_append(v___x_2649_, v___y_2634_);
                crate::leanh::lean_dec_ref(v___y_2634_);
                crate::leanh::lean_inc_ref(v_putStr_2635_);
                crate::leanh::lean_inc_ref(v___x_2650_);
                v___x_2651_ = crate::leanh::lean_apply_2(
                    v_putStr_2635_,
                    v___x_2650_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2651_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2651_, 1);
                    crate::leanh::lean_dec_ref(v___x_2650_);
                    state = 5;
                    continue;
                } else {
                    v_a_2652_ = crate::leanh::lean_ctor_get(v___x_2651_, 0);
                    v_isSharedCheck_2679_ = (!crate::leanh::lean_is_exclusive(v___x_2651_)) as u8;
                    if v_isSharedCheck_2679_ == 0 {
                        v___x_2654_ = v___x_2651_;
                        v_isShared_2655_ = v_isSharedCheck_2679_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2652_);
                        crate::leanh::lean_dec(v___x_2651_);
                        v___x_2654_ = crate::leanh::lean_box(0);
                        v_isShared_2655_ = v_isSharedCheck_2679_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2656_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                v___x_2657_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                v___x_2658_ = crate::leanh::lean_unsigned_to_nat(89);
                v___x_2659_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2660_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
                v___x_2661_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2662_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
                v___x_2663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_2662_,
                    v_useAnsi_2605_,
                );
                v___x_2664_ = lean_string_append(v___x_2660_, v___x_2663_);
                crate::leanh::lean_dec_ref(v___x_2663_);
                v___x_2665_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
                v___x_2666_ = lean_string_append(v___x_2664_, v___x_2665_);
                v___x_2667_ = lean_io_error_to_string(v_a_2652_);
                v___x_2668_ = lean_string_append(v___x_2666_, v___x_2667_);
                crate::leanh::lean_dec_ref(v___x_2667_);
                v___x_2669_ = lean_string_append(v___x_2668_, v___x_2648_);
                v___x_2670_ = l_String_quote(v___x_2650_);
                if v_isShared_2655_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2654_, 3);
                    crate::leanh::lean_ctor_set(v___x_2654_, 0, v___x_2670_);
                    v___x_2672_ = v___x_2654_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2678_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2670_);
                    v___x_2672_ = v_reuseFailAlloc_2678_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2673_ = l_Std_Format_defWidth;
                v___x_2674_ =
                    l_Std_Format_pretty(v___x_2672_, v___x_2673_, v___x_2661_, v___x_2661_);
                v___x_2675_ = lean_string_append(v___x_2669_, v___x_2674_);
                crate::leanh::lean_dec_ref(v___x_2674_);
                v___x_2676_ = l_mkPanicMessageWithDecl(
                    v___x_2656_,
                    v___x_2657_,
                    v___x_2658_,
                    v___x_2659_,
                    v___x_2675_,
                );
                crate::leanh::lean_dec_ref(v___x_2675_);
                v___x_2677_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2676_);
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___boxed(
    mut v_running_2702_: *mut crate::leanh::LeanObject,
    mut v_unfinished_2703_: *mut crate::leanh::LeanObject,
    mut v_a_2704_: *mut crate::leanh::LeanObject,
    mut v_a_2705_: *mut crate::leanh::LeanObject,
    mut v_a_2706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2707_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(
        v_running_2702_,
        v_unfinished_2703_,
        v_a_2704_,
        v_a_2705_,
    );
    crate::leanh::lean_dec_ref(v_a_2704_);
    crate::leanh::lean_dec_ref(v_unfinished_2703_);
    crate::leanh::lean_dec_ref(v_running_2702_);
    return v_res_2707_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(
    mut v_running_2708_: *mut crate::leanh::LeanObject,
    mut v_unfinished_2709_: *mut crate::leanh::LeanObject,
    mut v_h_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2714_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(
        v_running_2708_,
        v_unfinished_2709_,
        v_a_2711_,
        v_a_2712_,
    );
    return v___x_2714_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___boxed(
    mut v_running_2715_: *mut crate::leanh::LeanObject,
    mut v_unfinished_2716_: *mut crate::leanh::LeanObject,
    mut v_h_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
    mut v_a_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2721_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress(
        v_running_2715_,
        v_unfinished_2716_,
        v_h_2717_,
        v_a_2718_,
        v_a_2719_,
    );
    crate::leanh::lean_dec_ref(v_a_2718_);
    crate::leanh::lean_dec_ref(v_unfinished_2716_);
    crate::leanh::lean_dec_ref(v_running_2715_);
    return v_res_2721_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(
    mut v_ms_2725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: u8 = 0;
    v___x_2726_ = crate::leanh::lean_unsigned_to_nat(10000);
    v___x_2727_ = lean_nat_dec_lt(v___x_2726_, v_ms_2725_);
    if v___x_2727_ == 0 {
        let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2729_: u8 = 0;
        v___x_2728_ = crate::leanh::lean_unsigned_to_nat(1000);
        v___x_2729_ = lean_nat_dec_lt(v___x_2728_, v_ms_2725_);
        if v___x_2729_ == 0 {
            let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2730_ = l_Nat_reprFast(v_ms_2725_);
            v___x_2731_ =
                l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__0;
            v___x_2732_ = lean_string_append(v___x_2730_, v___x_2731_);
            return v___x_2732_;
        } else {
            let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2733_ = lean_nat_div(v_ms_2725_, v___x_2728_);
            v___x_2734_ = l_Nat_reprFast(v___x_2733_);
            v___x_2735_ =
                l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__1;
            v___x_2736_ = lean_string_append(v___x_2734_, v___x_2735_);
            v___x_2737_ = crate::leanh::lean_unsigned_to_nat(50);
            v___x_2738_ = lean_nat_add(v_ms_2725_, v___x_2737_);
            crate::leanh::lean_dec(v_ms_2725_);
            v___x_2739_ = crate::leanh::lean_unsigned_to_nat(100);
            v___x_2740_ = lean_nat_div(v___x_2738_, v___x_2739_);
            crate::leanh::lean_dec(v___x_2738_);
            v___x_2741_ = crate::leanh::lean_unsigned_to_nat(10);
            v___x_2742_ = lean_nat_mod(v___x_2740_, v___x_2741_);
            crate::leanh::lean_dec(v___x_2740_);
            v___x_2743_ = l_Nat_reprFast(v___x_2742_);
            v___x_2744_ = lean_string_append(v___x_2736_, v___x_2743_);
            crate::leanh::lean_dec_ref(v___x_2743_);
            v___x_2745_ =
                l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2;
            v___x_2746_ = lean_string_append(v___x_2744_, v___x_2745_);
            return v___x_2746_;
        }
    } else {
        let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2747_ = crate::leanh::lean_unsigned_to_nat(1000);
        v___x_2748_ = lean_nat_div(v_ms_2725_, v___x_2747_);
        crate::leanh::lean_dec(v_ms_2725_);
        v___x_2749_ = l_Nat_reprFast(v___x_2748_);
        v___x_2750_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime___closed__2;
        v___x_2751_ = lean_string_append(v___x_2749_, v___x_2750_);
        return v___x_2751_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(
    mut v_out_2752_: *mut crate::leanh::LeanObject,
    mut v___y_2753_: u8,
    mut v_useAnsi_2754_: u8,
    mut v_as_2755_: *mut crate::leanh::LeanObject,
    mut v_i_2756_: usize,
    mut v_stop_2757_: usize,
    mut v_b_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: usize = 0;
    let mut v___x_2765_: usize = 0;
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2761_ = lean_usize_dec_eq(v_i_2756_, v_stop_2757_);
                if v___x_2761_ == 0 {
                    v___x_2762_ = lean_array_uget_borrowed(v_as_2755_, v_i_2756_);
                    crate::leanh::lean_inc_ref(v_out_2752_);
                    v___x_2763_ =
                        l_Lake_logToStream(v___x_2762_, v_out_2752_, v___y_2753_, v_useAnsi_2754_);
                    v___x_2764_ = 1usize;
                    v___x_2765_ = lean_usize_add(v_i_2756_, v___x_2764_);
                    v_i_2756_ = v___x_2765_;
                    v_b_2758_ = v___x_2763_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_out_2752_);
                    v___x_2767_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v_b_2758_);
                    crate::leanh::lean_ctor_set(v___x_2767_, 1, v___y_2759_);
                    return v___x_2767_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg___boxed(
    mut v_out_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_2770_: *mut crate::leanh::LeanObject,
    mut v_as_2771_: *mut crate::leanh::LeanObject,
    mut v_i_2772_: *mut crate::leanh::LeanObject,
    mut v_stop_2773_: *mut crate::leanh::LeanObject,
    mut v_b_2774_: *mut crate::leanh::LeanObject,
    mut v___y_2775_: *mut crate::leanh::LeanObject,
    mut v___y_2776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_16424__boxed_2777_: u8 = 0;
    let mut v_useAnsi_16425__boxed_2778_: u8 = 0;
    let mut v_i_boxed_2779_: usize = 0;
    let mut v_stop_boxed_2780_: usize = 0;
    let mut v_res_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_16424__boxed_2777_ = (crate::leanh::lean_unbox(v___y_2769_) as u8);
    v_useAnsi_16425__boxed_2778_ = (crate::leanh::lean_unbox(v_useAnsi_2770_) as u8);
    v_i_boxed_2779_ = crate::leanh::lean_unbox_usize(v_i_2772_);
    crate::leanh::lean_dec(v_i_2772_);
    v_stop_boxed_2780_ = crate::leanh::lean_unbox_usize(v_stop_2773_);
    crate::leanh::lean_dec(v_stop_2773_);
    v_res_2781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_2768_, v___y_16424__boxed_2777_, v_useAnsi_16425__boxed_2778_, v_as_2771_, v_i_boxed_2779_, v_stop_boxed_2780_, v_b_2774_, v___y_2775_);
    crate::leanh::lean_dec_ref(v_as_2771_);
    return v_res_2781_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(
    mut v_job_2789_: *mut crate::leanh::LeanObject,
    mut v_a_2790_: *mut crate::leanh::LeanObject,
    mut v_a_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jobNo_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalJobs_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_2815_: u8 = 0;
    let mut v_failures_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resetCtrl_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUpdate_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spinnerIdx_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_outLv_2821_: u8 = 0;
    let mut v_failLv_2822_: u8 = 0;
    let mut v_minAction_2823_: u8 = 0;
    let mut v_showOptional_2824_: u8 = 0;
    let mut v_useAnsi_2825_: u8 = 0;
    let mut v_showProgress_2826_: u8 = 0;
    let mut v_showTime_2827_: u8 = 0;
    let mut v___y_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: u8 = 0;
    let mut v___x_2835_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: u8 = 0;
    let mut v___x_2838_: usize = 0;
    let mut v___x_2839_: usize = 0;
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: usize = 0;
    let mut v___x_2842_: usize = 0;
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2846_: u8 = 0;
    let mut v___y_2847_: u8 = 0;
    let mut v___y_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: u8 = 0;
    let mut v___y_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2855_: u8 = 0;
    let mut v___y_2856_: u8 = 0;
    let mut v___y_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2859_: u8 = 0;
    let mut v___y_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jobNo_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalJobs_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_2866_: u8 = 0;
    let mut v_failures_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resetCtrl_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUpdate_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spinnerIdx_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2873_: u8 = 0;
    let mut v_putStr_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2885_: u8 = 0;
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut v_reuseFailAlloc_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v___y_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2919_: u8 = 0;
    let mut v___y_2920_: u8 = 0;
    let mut v___y_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2922_: u8 = 0;
    let mut v___y_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_2931_: u8 = 0;
    let mut v___y_2933_: u8 = 0;
    let mut v___y_2934_: u8 = 0;
    let mut v___y_2935_: u32 = 0;
    let mut v___y_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: u8 = 0;
    let mut v___y_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2944_: u8 = 0;
    let mut v___y_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2968_: u8 = 0;
    let mut v___y_2969_: u8 = 0;
    let mut v___y_2970_: u32 = 0;
    let mut v___y_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: u8 = 0;
    let mut v___y_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2979_: u8 = 0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2982_: u8 = 0;
    let mut v___y_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2984_: u8 = 0;
    let mut v___y_2985_: u32 = 0;
    let mut v___y_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2989_: u8 = 0;
    let mut v___y_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2993_: u8 = 0;
    let mut v___y_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: u8 = 0;
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3003_: u8 = 0;
    let mut v___y_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3005_: u8 = 0;
    let mut v___y_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3008_: u8 = 0;
    let mut v___y_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3012_: u8 = 0;
    let mut v___y_3013_: u32 = 0;
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: u8 = 0;
    let mut v___y_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: u8 = 0;
    let mut v___y_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3023_: u8 = 0;
    let mut v___y_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3026_: u8 = 0;
    let mut v___y_3027_: u8 = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: u32 = 0;
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: u32 = 0;
    let mut v___y_3033_: u8 = 0;
    let mut v___y_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3035_: u8 = 0;
    let mut v___y_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3040_: u8 = 0;
    let mut v___y_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3042_: u8 = 0;
    let mut v___y_3043_: u8 = 0;
    let mut v___y_3045_: u8 = 0;
    let mut v___y_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3047_: u8 = 0;
    let mut v___y_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3050_: u8 = 0;
    let mut v___y_3051_: u8 = 0;
    let mut v___y_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3053_: u8 = 0;
    let mut v___y_3054_: u8 = 0;
    let mut v___y_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jobNo_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalJobs_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_3059_: u8 = 0;
    let mut v_failures_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resetCtrl_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUpdate_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spinnerIdx_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut v___y_3073_: u8 = 0;
    let mut v___y_3074_: u8 = 0;
    let mut v___y_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3076_: u8 = 0;
    let mut v___y_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3079_: u8 = 0;
    let mut v___y_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3081_: u8 = 0;
    let mut v___y_3082_: u8 = 0;
    let mut v___y_3083_: u8 = 0;
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3086_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3090_: u8 = 0;
    let mut v_unused_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3098_: u8 = 0;
    let mut v___y_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3100_: u8 = 0;
    let mut v___y_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: u8 = 0;
    let mut v___y_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3104_: u8 = 0;
    let mut v___y_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3106_: u8 = 0;
    let mut v___y_3107_: u8 = 0;
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: u8 = 0;
    let mut v___y_3112_: u8 = 0;
    let mut v___y_3113_: u8 = 0;
    let mut v___y_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3118_: u8 = 0;
    let mut v___y_3119_: u8 = 0;
    let mut v___y_3120_: u8 = 0;
    let mut v___x_3121_: u8 = 0;
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: u8 = 0;
    let mut v___x_3124_: u8 = 0;
    let mut v___y_3126_: u8 = 0;
    let mut v___y_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3128_: u8 = 0;
    let mut v___y_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3132_: u8 = 0;
    let mut v___y_3133_: u8 = 0;
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: u8 = 0;
    let mut v___y_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3140_: u8 = 0;
    let mut v_wantsRebuild_3141_: u8 = 0;
    let mut v_buildTime_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: u8 = 0;
    let mut v___x_3147_: u8 = 0;
    let mut v___x_3148_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_jobNo_2813_ = crate::leanh::lean_ctor_get(v_a_2791_, 0);
                crate::leanh::lean_inc(v_jobNo_2813_);
                v_totalJobs_2814_ = crate::leanh::lean_ctor_get(v_a_2791_, 1);
                crate::leanh::lean_inc(v_totalJobs_2814_);
                v_wantsRebuild_2815_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2791_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_failures_2816_ = crate::leanh::lean_ctor_get(v_a_2791_, 2);
                v_resetCtrl_2817_ = crate::leanh::lean_ctor_get(v_a_2791_, 3);
                v_lastUpdate_2818_ = crate::leanh::lean_ctor_get(v_a_2791_, 4);
                v_spinnerIdx_2819_ = crate::leanh::lean_ctor_get(v_a_2791_, 5);
                v_out_2820_ = crate::leanh::lean_ctor_get(v_a_2790_, 1);
                v_outLv_2821_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_failLv_2822_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_minAction_2823_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_showOptional_2824_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_useAnsi_2825_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                );
                v_showProgress_2826_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                );
                v_showTime_2827_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2790_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
                );
                v_task_2929_ = crate::leanh::lean_ctor_get(v_job_2789_, 0);
                crate::leanh::lean_inc_ref(v_task_2929_);
                v_caption_2930_ = crate::leanh::lean_ctor_get(v_job_2789_, 2);
                crate::leanh::lean_inc_ref(v_caption_2930_);
                v_optional_2931_ = crate::leanh::lean_ctor_get_uint8(
                    v_job_2789_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_job_2789_);
                v___x_3149_ = lean_task_get_own(v_task_2929_);
                v_a_3150_ = crate::leanh::lean_ctor_get(v___x_3149_, 1);
                crate::leanh::lean_inc(v_a_3150_);
                crate::leanh::lean_dec(v___x_3149_);
                v___y_3138_ = v_a_3150_;
                state = 28;
                continue;
            }
            1 => {
                v___x_2795_ = crate::leanh::lean_box(0);
                v___x_2796_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2796_, 0, v___x_2795_);
                crate::leanh::lean_ctor_set(v___x_2796_, 1, v___y_2794_);
                return v___x_2796_;
            }
            2 => {
                v___x_2800_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2800_, 0, v_val_2799_);
                crate::leanh::lean_ctor_set(v___x_2800_, 1, v___y_2798_);
                return v___x_2800_;
            }
            3 => {
                v_out_2804_ = crate::leanh::lean_ctor_get(v___y_2802_, 1);
                v_flush_2805_ = crate::leanh::lean_ctor_get(v_out_2804_, 0);
                crate::leanh::lean_inc_ref(v_flush_2805_);
                v___x_2806_ = crate::leanh::lean_apply_1(v_flush_2805_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_2806_) == 0 {
                    v_a_2807_ = crate::leanh::lean_ctor_get(v___x_2806_, 0);
                    crate::leanh::lean_inc(v_a_2807_);
                    crate::leanh::lean_dec_ref_known(v___x_2806_, 1);
                    v___y_2798_ = v___y_2803_;
                    v_val_2799_ = v_a_2807_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2806_, 1);
                    v___x_2808_ = crate::leanh::lean_box(0);
                    v___y_2798_ = v___y_2803_;
                    v_val_2799_ = v___x_2808_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_snd_2812_ = crate::leanh::lean_ctor_get(v___y_2811_, 1);
                crate::leanh::lean_inc(v_snd_2812_);
                crate::leanh::lean_dec_ref(v___y_2811_);
                v___y_2802_ = v___y_2810_;
                v___y_2803_ = v_snd_2812_;
                state = 3;
                continue;
            }
            5 => {
                v___x_2835_ = lean_nat_dec_lt(v___y_2833_, v___y_2829_);
                crate::leanh::lean_dec(v___y_2833_);
                if v___x_2835_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2830_);
                    crate::leanh::lean_dec(v___y_2829_);
                    v___y_2802_ = v___y_2832_;
                    v___y_2803_ = v___y_2831_;
                    state = 3;
                    continue;
                } else {
                    v___x_2836_ = crate::leanh::lean_box(0);
                    v___x_2837_ = lean_nat_dec_le(v___y_2829_, v___y_2829_);
                    if v___x_2837_ == 0 {
                        if v___x_2835_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_2830_);
                            crate::leanh::lean_dec(v___y_2829_);
                            v___y_2802_ = v___y_2832_;
                            v___y_2803_ = v___y_2831_;
                            state = 3;
                            continue;
                        } else {
                            v___x_2838_ = 0usize;
                            v___x_2839_ = lean_usize_of_nat(v___y_2829_);
                            crate::leanh::lean_dec(v___y_2829_);
                            crate::leanh::lean_inc_ref(v_out_2820_);
                            v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_2820_, v___y_2834_, v_useAnsi_2825_, v___y_2830_, v___x_2838_, v___x_2839_, v___x_2836_, v___y_2831_);
                            crate::leanh::lean_dec_ref(v___y_2830_);
                            v___y_2810_ = v___y_2832_;
                            v___y_2811_ = v___x_2840_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_2841_ = 0usize;
                        v___x_2842_ = lean_usize_of_nat(v___y_2829_);
                        crate::leanh::lean_dec(v___y_2829_);
                        crate::leanh::lean_inc_ref(v_out_2820_);
                        v___x_2843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_2820_, v___y_2834_, v_useAnsi_2825_, v___y_2830_, v___x_2841_, v___x_2842_, v___x_2836_, v___y_2831_);
                        crate::leanh::lean_dec_ref(v___y_2830_);
                        v___y_2810_ = v___y_2832_;
                        v___y_2811_ = v___x_2843_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                if v___y_2847_ == 0 {
                    crate::leanh::lean_dec(v___y_2851_);
                    crate::leanh::lean_dec_ref(v___y_2848_);
                    crate::leanh::lean_dec(v___y_2845_);
                    v___y_2802_ = v___y_2850_;
                    v___y_2803_ = v___y_2849_;
                    state = 3;
                    continue;
                } else {
                    if v___y_2846_ == 0 {
                        v___y_2829_ = v___y_2845_;
                        v___y_2830_ = v___y_2848_;
                        v___y_2831_ = v___y_2849_;
                        v___y_2832_ = v___y_2850_;
                        v___y_2833_ = v___y_2851_;
                        v___y_2834_ = v_outLv_2821_;
                        state = 5;
                        continue;
                    } else {
                        v___x_2852_ = 0;
                        v___y_2829_ = v___y_2845_;
                        v___y_2830_ = v___y_2848_;
                        v___y_2831_ = v___y_2849_;
                        v___y_2832_ = v___y_2850_;
                        v___y_2833_ = v___y_2851_;
                        v___y_2834_ = v___x_2852_;
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                v_out_2863_ = crate::leanh::lean_ctor_get(v___y_2860_, 1);
                v_jobNo_2864_ = crate::leanh::lean_ctor_get(v___y_2857_, 0);
                v_totalJobs_2865_ = crate::leanh::lean_ctor_get(v___y_2857_, 1);
                v_wantsRebuild_2866_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2857_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_failures_2867_ = crate::leanh::lean_ctor_get(v___y_2857_, 2);
                v_resetCtrl_2868_ = crate::leanh::lean_ctor_get(v___y_2857_, 3);
                v_lastUpdate_2869_ = crate::leanh::lean_ctor_get(v___y_2857_, 4);
                v_spinnerIdx_2870_ = crate::leanh::lean_ctor_get(v___y_2857_, 5);
                v_isSharedCheck_2916_ = (!crate::leanh::lean_is_exclusive(v___y_2857_)) as u8;
                if v_isSharedCheck_2916_ == 0 {
                    v___x_2872_ = v___y_2857_;
                    v_isShared_2873_ = v_isSharedCheck_2916_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_spinnerIdx_2870_);
                    crate::leanh::lean_inc(v_lastUpdate_2869_);
                    crate::leanh::lean_inc(v_resetCtrl_2868_);
                    crate::leanh::lean_inc(v_failures_2867_);
                    crate::leanh::lean_inc(v_totalJobs_2865_);
                    crate::leanh::lean_inc(v_jobNo_2864_);
                    crate::leanh::lean_dec(v___y_2857_);
                    v___x_2872_ = crate::leanh::lean_box(0);
                    v_isShared_2873_ = v_isSharedCheck_2916_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_putStr_2874_ = crate::leanh::lean_ctor_get(v_out_2863_, 4);
                v___x_2875_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
                if v_isShared_2873_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2872_, 3, v___x_2875_);
                    v___x_2877_ = v___x_2872_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_jobNo_2864_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_totalJobs_2865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 2, v_failures_2867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 3, v___x_2875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 4, v_lastUpdate_2869_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 5, v_spinnerIdx_2870_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2915_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        v_wantsRebuild_2866_,
                    );
                    v___x_2877_ = v_reuseFailAlloc_2915_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2878_ = lean_string_append(v_resetCtrl_2868_, v___y_2862_);
                crate::leanh::lean_dec_ref(v___y_2862_);
                v___x_2879_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
                v___x_2880_ = lean_string_append(v___x_2878_, v___x_2879_);
                crate::leanh::lean_inc_ref(v_putStr_2874_);
                crate::leanh::lean_inc_ref(v___x_2880_);
                v___x_2881_ = crate::leanh::lean_apply_2(
                    v_putStr_2874_,
                    v___x_2880_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2881_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2881_, 1);
                    crate::leanh::lean_dec_ref(v___x_2880_);
                    v___y_2845_ = v___y_2854_;
                    v___y_2846_ = v___y_2856_;
                    v___y_2847_ = v___y_2859_;
                    v___y_2848_ = v___y_2858_;
                    v___y_2849_ = v___x_2877_;
                    v___y_2850_ = v___y_2860_;
                    v___y_2851_ = v___y_2861_;
                    state = 6;
                    continue;
                } else {
                    v_a_2882_ = crate::leanh::lean_ctor_get(v___x_2881_, 0);
                    v_isSharedCheck_2914_ = (!crate::leanh::lean_is_exclusive(v___x_2881_)) as u8;
                    if v_isSharedCheck_2914_ == 0 {
                        v___x_2884_ = v___x_2881_;
                        v_isShared_2885_ = v_isSharedCheck_2914_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2882_);
                        crate::leanh::lean_dec(v___x_2881_);
                        v___x_2884_ = crate::leanh::lean_box(0);
                        v_isShared_2885_ = v_isSharedCheck_2914_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                v___x_2886_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                v___x_2887_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                v___x_2888_ = crate::leanh::lean_unsigned_to_nat(89);
                v___x_2889_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2890_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
                v___x_2891_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__6;
                v___x_2892_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__11;
                crate::leanh::lean_inc(v___y_2861_);
                v___x_2893_ = l_Lean_Name_num___override(v___x_2892_, v___y_2861_);
                v___x_2894_ = l_Lean_Name_str___override(v___x_2893_, v___x_2891_);
                v___x_2895_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__14;
                v___x_2896_ = l_Lean_Name_str___override(v___x_2894_, v___x_2895_);
                v___x_2897_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_2896_,
                    v___y_2855_,
                );
                v___x_2898_ = lean_string_append(v___x_2890_, v___x_2897_);
                crate::leanh::lean_dec_ref(v___x_2897_);
                v___x_2899_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
                v___x_2900_ = lean_string_append(v___x_2898_, v___x_2899_);
                v___x_2901_ = lean_io_error_to_string(v_a_2882_);
                v___x_2902_ = lean_string_append(v___x_2900_, v___x_2901_);
                crate::leanh::lean_dec_ref(v___x_2901_);
                v___x_2903_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                v___x_2904_ = lean_string_append(v___x_2902_, v___x_2903_);
                v___x_2905_ = l_String_quote(v___x_2880_);
                if v_isShared_2885_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2884_, 3);
                    crate::leanh::lean_ctor_set(v___x_2884_, 0, v___x_2905_);
                    v___x_2907_ = v___x_2884_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2905_);
                    v___x_2907_ = v_reuseFailAlloc_2913_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2908_ = l_Std_Format_defWidth;
                crate::leanh::lean_inc_n(v___y_2861_, 2);
                v___x_2909_ =
                    l_Std_Format_pretty(v___x_2907_, v___x_2908_, v___y_2861_, v___y_2861_);
                v___x_2910_ = lean_string_append(v___x_2904_, v___x_2909_);
                crate::leanh::lean_dec_ref(v___x_2909_);
                v___x_2911_ = l_mkPanicMessageWithDecl(
                    v___x_2886_,
                    v___x_2887_,
                    v___x_2888_,
                    v___x_2889_,
                    v___x_2910_,
                );
                crate::leanh::lean_dec_ref(v___x_2910_);
                v___x_2912_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_2911_);
                v___y_2845_ = v___y_2854_;
                v___y_2846_ = v___y_2856_;
                v___y_2847_ = v___y_2859_;
                v___y_2848_ = v___y_2858_;
                v___y_2849_ = v___x_2877_;
                v___y_2850_ = v___y_2860_;
                v___y_2851_ = v___y_2861_;
                state = 6;
                continue;
            }
            12 => {
                v___x_2928_ = l_Lake_Ansi_chalk(v___y_2927_, v___y_2924_);
                crate::leanh::lean_dec_ref(v___y_2924_);
                crate::leanh::lean_dec_ref(v___y_2927_);
                v___y_2854_ = v___y_2918_;
                v___y_2855_ = v___y_2920_;
                v___y_2856_ = v___y_2919_;
                v___y_2857_ = v___y_2921_;
                v___y_2858_ = v___y_2923_;
                v___y_2859_ = v___y_2922_;
                v___y_2860_ = v___y_2925_;
                v___y_2861_ = v___y_2926_;
                v___y_2862_ = v___x_2928_;
                state = 7;
                continue;
            }
            13 => {
                v___x_2946_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
                v___x_2947_ = lean_string_push(v___x_2946_, v___y_2935_);
                v___x_2948_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__2;
                v___x_2949_ = lean_string_append(v___x_2947_, v___x_2948_);
                v___x_2950_ = l_Nat_reprFast(v_jobNo_2813_);
                v___x_2951_ = lean_string_append(v___x_2949_, v___x_2950_);
                crate::leanh::lean_dec_ref(v___x_2950_);
                v___x_2952_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__3;
                v___x_2953_ = lean_string_append(v___x_2951_, v___x_2952_);
                v___x_2954_ = l_Nat_reprFast(v_totalJobs_2814_);
                v___x_2955_ = lean_string_append(v___x_2953_, v___x_2954_);
                crate::leanh::lean_dec_ref(v___x_2954_);
                v___x_2956_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__1;
                v___x_2957_ = lean_string_append(v___x_2955_, v___x_2956_);
                v___x_2958_ = lean_string_append(v___x_2957_, v___y_2939_);
                v___x_2959_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__2;
                v___x_2960_ = lean_string_append(v___x_2958_, v___x_2959_);
                v___x_2961_ = lean_string_append(v___x_2960_, v___y_2937_);
                crate::leanh::lean_dec_ref(v___y_2937_);
                v___x_2962_ = lean_string_append(v___x_2961_, v___x_2959_);
                v___x_2963_ = lean_string_append(v___x_2962_, v_caption_2930_);
                crate::leanh::lean_dec_ref(v_caption_2930_);
                v___x_2964_ = lean_string_append(v___x_2963_, v___y_2945_);
                crate::leanh::lean_dec_ref(v___y_2945_);
                if v_useAnsi_2825_ == 0 {
                    v___y_2854_ = v___y_2938_;
                    v___y_2855_ = v___y_2940_;
                    v___y_2856_ = v___y_2933_;
                    v___y_2857_ = v___y_2941_;
                    v___y_2858_ = v___y_2942_;
                    v___y_2859_ = v___y_2934_;
                    v___y_2860_ = v___y_2936_;
                    v___y_2861_ = v___y_2943_;
                    v___y_2862_ = v___x_2964_;
                    state = 7;
                    continue;
                } else {
                    if v___y_2934_ == 0 {
                        v___x_2965_ =
                            l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__3;
                        v___y_2918_ = v___y_2938_;
                        v___y_2919_ = v___y_2933_;
                        v___y_2920_ = v___y_2940_;
                        v___y_2921_ = v___y_2941_;
                        v___y_2922_ = v___y_2934_;
                        v___y_2923_ = v___y_2942_;
                        v___y_2924_ = v___x_2964_;
                        v___y_2925_ = v___y_2936_;
                        v___y_2926_ = v___y_2943_;
                        v___y_2927_ = v___x_2965_;
                        state = 12;
                        continue;
                    } else {
                        v___x_2966_ = l_Lake_LogLevel_ansiColor(v___y_2944_);
                        v___y_2918_ = v___y_2938_;
                        v___y_2919_ = v___y_2933_;
                        v___y_2920_ = v___y_2940_;
                        v___y_2921_ = v___y_2941_;
                        v___y_2922_ = v___y_2934_;
                        v___y_2923_ = v___y_2942_;
                        v___y_2924_ = v___x_2964_;
                        v___y_2925_ = v___y_2936_;
                        v___y_2926_ = v___y_2943_;
                        v___y_2927_ = v___x_2966_;
                        state = 12;
                        continue;
                    }
                }
            }
            14 => {
                v___x_2980_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
                v___y_2933_ = v___y_2968_;
                v___y_2934_ = v___y_2969_;
                v___y_2935_ = v___y_2970_;
                v___y_2936_ = v___y_2971_;
                v___y_2937_ = v___y_2972_;
                v___y_2938_ = v___y_2973_;
                v___y_2939_ = v___y_2974_;
                v___y_2940_ = v___y_2975_;
                v___y_2941_ = v___y_2976_;
                v___y_2942_ = v___y_2977_;
                v___y_2943_ = v___y_2978_;
                v___y_2944_ = v___y_2979_;
                v___y_2945_ = v___x_2980_;
                state = 13;
                continue;
            }
            15 => {
                if v_showTime_2827_ == 0 {
                    crate::leanh::lean_dec(v___y_2983_);
                    v___y_2968_ = v___y_2982_;
                    v___y_2969_ = v___y_2984_;
                    v___y_2970_ = v___y_2985_;
                    v___y_2971_ = v___y_2986_;
                    v___y_2972_ = v___y_2987_;
                    v___y_2973_ = v___y_2988_;
                    v___y_2974_ = v___y_2994_;
                    v___y_2975_ = v___y_2989_;
                    v___y_2976_ = v___y_2990_;
                    v___y_2977_ = v___y_2991_;
                    v___y_2978_ = v___y_2992_;
                    v___y_2979_ = v___y_2993_;
                    state = 14;
                    continue;
                } else {
                    v___x_2995_ = lean_nat_dec_lt(v___y_2992_, v___y_2983_);
                    if v___x_2995_ == 0 {
                        crate::leanh::lean_dec(v___y_2983_);
                        v___y_2968_ = v___y_2982_;
                        v___y_2969_ = v___y_2984_;
                        v___y_2970_ = v___y_2985_;
                        v___y_2971_ = v___y_2986_;
                        v___y_2972_ = v___y_2987_;
                        v___y_2973_ = v___y_2988_;
                        v___y_2974_ = v___y_2994_;
                        v___y_2975_ = v___y_2989_;
                        v___y_2976_ = v___y_2990_;
                        v___y_2977_ = v___y_2991_;
                        v___y_2978_ = v___y_2992_;
                        v___y_2979_ = v___y_2993_;
                        state = 14;
                        continue;
                    } else {
                        v___x_2996_ =
                            l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__4;
                        v___x_2997_ =
                            l___private_Lake_Build_Run_0__Lake_Monitor_reportJob_formatTime(
                                v___y_2983_,
                            );
                        v___x_2998_ = lean_string_append(v___x_2996_, v___x_2997_);
                        crate::leanh::lean_dec_ref(v___x_2997_);
                        v___x_2999_ =
                            l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__5;
                        v___x_3000_ = lean_string_append(v___x_2998_, v___x_2999_);
                        v___y_2933_ = v___y_2982_;
                        v___y_2934_ = v___y_2984_;
                        v___y_2935_ = v___y_2985_;
                        v___y_2936_ = v___y_2986_;
                        v___y_2937_ = v___y_2987_;
                        v___y_2938_ = v___y_2988_;
                        v___y_2939_ = v___y_2994_;
                        v___y_2940_ = v___y_2989_;
                        v___y_2941_ = v___y_2990_;
                        v___y_2942_ = v___y_2991_;
                        v___y_2943_ = v___y_2992_;
                        v___y_2944_ = v___y_2993_;
                        v___y_2945_ = v___x_3000_;
                        state = 13;
                        continue;
                    }
                }
            }
            16 => {
                if v_optional_2931_ == 0 {
                    v___x_3014_ = l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
                    v___y_2982_ = v___y_3005_;
                    v___y_2983_ = v___y_3004_;
                    v___y_2984_ = v___y_3008_;
                    v___y_2985_ = v___y_3013_;
                    v___y_2986_ = v___y_3009_;
                    v___y_2987_ = v___y_3010_;
                    v___y_2988_ = v___y_3002_;
                    v___y_2989_ = v___y_3003_;
                    v___y_2990_ = v___y_3006_;
                    v___y_2991_ = v___y_3007_;
                    v___y_2992_ = v___y_3011_;
                    v___y_2993_ = v___y_3012_;
                    v___y_2994_ = v___x_3014_;
                    state = 15;
                    continue;
                } else {
                    v___x_3015_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__6;
                    v___y_2982_ = v___y_3005_;
                    v___y_2983_ = v___y_3004_;
                    v___y_2984_ = v___y_3008_;
                    v___y_2985_ = v___y_3013_;
                    v___y_2986_ = v___y_3009_;
                    v___y_2987_ = v___y_3010_;
                    v___y_2988_ = v___y_3002_;
                    v___y_2989_ = v___y_3003_;
                    v___y_2990_ = v___y_3006_;
                    v___y_2991_ = v___y_3007_;
                    v___y_2992_ = v___y_3011_;
                    v___y_2993_ = v___y_3012_;
                    v___y_2994_ = v___x_3015_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                if v___y_3023_ == 0 {
                    if v_showProgress_2826_ == 0 {
                        crate::leanh::lean_dec(v___y_3025_);
                        crate::leanh::lean_dec_ref(v___y_3022_);
                        crate::leanh::lean_dec(v___y_3020_);
                        crate::leanh::lean_dec(v___y_3018_);
                        crate::leanh::lean_dec_ref(v_caption_2930_);
                        crate::leanh::lean_dec(v_totalJobs_2814_);
                        crate::leanh::lean_dec(v_jobNo_2813_);
                        v___y_2794_ = v___y_3021_;
                        state = 1;
                        continue;
                    } else {
                        if v_useAnsi_2825_ == 0 {
                            if v___y_3026_ == 0 {
                                crate::leanh::lean_dec(v___y_3025_);
                                crate::leanh::lean_dec_ref(v___y_3022_);
                                crate::leanh::lean_dec(v___y_3020_);
                                crate::leanh::lean_dec(v___y_3018_);
                                crate::leanh::lean_dec_ref(v_caption_2930_);
                                crate::leanh::lean_dec(v_totalJobs_2814_);
                                crate::leanh::lean_dec(v_jobNo_2813_);
                                v___y_2794_ = v___y_3021_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3028_ = l_Lake_JobAction_verb(v___y_3019_, v___y_3017_);
                                v___x_3029_ = 10004;
                                v___y_3002_ = v___y_3018_;
                                v___y_3003_ = v___y_3026_;
                                v___y_3004_ = v___y_3020_;
                                v___y_3005_ = v___y_3019_;
                                v___y_3006_ = v___y_3021_;
                                v___y_3007_ = v___y_3022_;
                                v___y_3008_ = v___y_3023_;
                                v___y_3009_ = v___y_3024_;
                                v___y_3010_ = v___x_3028_;
                                v___y_3011_ = v___y_3025_;
                                v___y_3012_ = v___y_3027_;
                                v___y_3013_ = v___x_3029_;
                                state = 16;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_3025_);
                            crate::leanh::lean_dec_ref(v___y_3022_);
                            crate::leanh::lean_dec(v___y_3020_);
                            crate::leanh::lean_dec(v___y_3018_);
                            crate::leanh::lean_dec_ref(v_caption_2930_);
                            crate::leanh::lean_dec(v_totalJobs_2814_);
                            crate::leanh::lean_dec(v_jobNo_2813_);
                            v___y_2794_ = v___y_3021_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3030_ = l_Lake_JobAction_verb(v___y_3019_, v___y_3017_);
                    v___x_3031_ = l_Lake_LogLevel_icon(v___y_3027_);
                    v___y_3002_ = v___y_3018_;
                    v___y_3003_ = v___y_3023_;
                    v___y_3004_ = v___y_3020_;
                    v___y_3005_ = v___y_3019_;
                    v___y_3006_ = v___y_3021_;
                    v___y_3007_ = v___y_3022_;
                    v___y_3008_ = v___y_3023_;
                    v___y_3009_ = v___y_3024_;
                    v___y_3010_ = v___x_3030_;
                    v___y_3011_ = v___y_3025_;
                    v___y_3012_ = v___y_3027_;
                    v___y_3013_ = v___x_3031_;
                    state = 16;
                    continue;
                }
            }
            18 => {
                if v_optional_2931_ == 0 {
                    v___y_3017_ = v___y_3033_;
                    v___y_3018_ = v___y_3034_;
                    v___y_3019_ = v___y_3035_;
                    v___y_3020_ = v___y_3036_;
                    v___y_3021_ = v___y_3037_;
                    v___y_3022_ = v___y_3038_;
                    v___y_3023_ = v___y_3043_;
                    v___y_3024_ = v___y_3039_;
                    v___y_3025_ = v___y_3041_;
                    v___y_3026_ = v___y_3040_;
                    v___y_3027_ = v___y_3042_;
                    state = 17;
                    continue;
                } else {
                    if v_showOptional_2824_ == 0 {
                        crate::leanh::lean_dec(v___y_3041_);
                        crate::leanh::lean_dec_ref(v___y_3038_);
                        crate::leanh::lean_dec(v___y_3036_);
                        crate::leanh::lean_dec(v___y_3034_);
                        crate::leanh::lean_dec_ref(v_caption_2930_);
                        crate::leanh::lean_dec(v_totalJobs_2814_);
                        crate::leanh::lean_dec(v_jobNo_2813_);
                        v___y_2794_ = v___y_3037_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3017_ = v___y_3033_;
                        v___y_3018_ = v___y_3034_;
                        v___y_3019_ = v___y_3035_;
                        v___y_3020_ = v___y_3036_;
                        v___y_3021_ = v___y_3037_;
                        v___y_3022_ = v___y_3038_;
                        v___y_3023_ = v___y_3043_;
                        v___y_3024_ = v___y_3039_;
                        v___y_3025_ = v___y_3041_;
                        v___y_3026_ = v___y_3040_;
                        v___y_3027_ = v___y_3042_;
                        state = 17;
                        continue;
                    }
                }
            }
            19 => {
                if v___y_3047_ == 0 {
                    if v___y_3053_ == 0 {
                        v___y_3033_ = v___y_3045_;
                        v___y_3034_ = v___y_3046_;
                        v___y_3035_ = v___y_3047_;
                        v___y_3036_ = v___y_3048_;
                        v___y_3037_ = v___y_3056_;
                        v___y_3038_ = v___y_3049_;
                        v___y_3039_ = v___y_3055_;
                        v___y_3040_ = v___y_3051_;
                        v___y_3041_ = v___y_3052_;
                        v___y_3042_ = v___y_3054_;
                        v___y_3043_ = v___y_3053_;
                        state = 18;
                        continue;
                    } else {
                        v___y_3033_ = v___y_3045_;
                        v___y_3034_ = v___y_3046_;
                        v___y_3035_ = v___y_3047_;
                        v___y_3036_ = v___y_3048_;
                        v___y_3037_ = v___y_3056_;
                        v___y_3038_ = v___y_3049_;
                        v___y_3039_ = v___y_3055_;
                        v___y_3040_ = v___y_3051_;
                        v___y_3041_ = v___y_3052_;
                        v___y_3042_ = v___y_3054_;
                        v___y_3043_ = v___y_3050_;
                        state = 18;
                        continue;
                    }
                } else {
                    if v_optional_2931_ == 0 {
                        v_jobNo_3057_ = crate::leanh::lean_ctor_get(v___y_3056_, 0);
                        v_totalJobs_3058_ = crate::leanh::lean_ctor_get(v___y_3056_, 1);
                        v_wantsRebuild_3059_ = crate::leanh::lean_ctor_get_uint8(
                            v___y_3056_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        );
                        v_failures_3060_ = crate::leanh::lean_ctor_get(v___y_3056_, 2);
                        v_resetCtrl_3061_ = crate::leanh::lean_ctor_get(v___y_3056_, 3);
                        v_lastUpdate_3062_ = crate::leanh::lean_ctor_get(v___y_3056_, 4);
                        v_spinnerIdx_3063_ = crate::leanh::lean_ctor_get(v___y_3056_, 5);
                        v_isSharedCheck_3071_ =
                            (!crate::leanh::lean_is_exclusive(v___y_3056_)) as u8;
                        if v_isSharedCheck_3071_ == 0 {
                            v___x_3065_ = v___y_3056_;
                            v_isShared_3066_ = v_isSharedCheck_3071_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_spinnerIdx_3063_);
                            crate::leanh::lean_inc(v_lastUpdate_3062_);
                            crate::leanh::lean_inc(v_resetCtrl_3061_);
                            crate::leanh::lean_inc(v_failures_3060_);
                            crate::leanh::lean_inc(v_totalJobs_3058_);
                            crate::leanh::lean_inc(v_jobNo_3057_);
                            crate::leanh::lean_dec(v___y_3056_);
                            v___x_3065_ = crate::leanh::lean_box(0);
                            v_isShared_3066_ = v_isSharedCheck_3071_;
                            state = 20;
                            continue;
                        }
                    } else {
                        v___y_3033_ = v___y_3045_;
                        v___y_3034_ = v___y_3046_;
                        v___y_3035_ = v___y_3047_;
                        v___y_3036_ = v___y_3048_;
                        v___y_3037_ = v___y_3056_;
                        v___y_3038_ = v___y_3049_;
                        v___y_3039_ = v___y_3055_;
                        v___y_3040_ = v___y_3051_;
                        v___y_3041_ = v___y_3052_;
                        v___y_3042_ = v___y_3054_;
                        v___y_3043_ = v___y_3047_;
                        state = 18;
                        continue;
                    }
                }
            }
            20 => {
                crate::leanh::lean_inc_ref(v_caption_2930_);
                v___x_3067_ = lean_array_push(v_failures_3060_, v_caption_2930_);
                if v_isShared_3066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3065_, 2, v___x_3067_);
                    v___x_3069_ = v___x_3065_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_jobNo_3057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_totalJobs_3058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 2, v___x_3067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 3, v_resetCtrl_3061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 4, v_lastUpdate_3062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 5, v_spinnerIdx_3063_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3070_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        v_wantsRebuild_3059_,
                    );
                    v___x_3069_ = v_reuseFailAlloc_3070_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___y_3033_ = v___y_3045_;
                v___y_3034_ = v___y_3046_;
                v___y_3035_ = v___y_3047_;
                v___y_3036_ = v___y_3048_;
                v___y_3037_ = v___x_3069_;
                v___y_3038_ = v___y_3049_;
                v___y_3039_ = v___y_3055_;
                v___y_3040_ = v___y_3051_;
                v___y_3041_ = v___y_3052_;
                v___y_3042_ = v___y_3054_;
                v___y_3043_ = v___y_3047_;
                state = 18;
                continue;
            }
            22 => {
                if v___y_3073_ == 0 {
                    v___y_3045_ = v___y_3074_;
                    v___y_3046_ = v___y_3075_;
                    v___y_3047_ = v___y_3076_;
                    v___y_3048_ = v___y_3077_;
                    v___y_3049_ = v___y_3078_;
                    v___y_3050_ = v___y_3079_;
                    v___y_3051_ = v___y_3083_;
                    v___y_3052_ = v___y_3080_;
                    v___y_3053_ = v___y_3081_;
                    v___y_3054_ = v___y_3082_;
                    v___y_3055_ = v_a_2790_;
                    v___y_3056_ = v_a_2791_;
                    state = 19;
                    continue;
                } else {
                    if v_wantsRebuild_2815_ == 0 {
                        crate::leanh::lean_inc(v_spinnerIdx_2819_);
                        crate::leanh::lean_inc(v_lastUpdate_2818_);
                        crate::leanh::lean_inc_ref(v_resetCtrl_2817_);
                        crate::leanh::lean_inc_ref(v_failures_2816_);
                        v_isSharedCheck_3090_ = (!crate::leanh::lean_is_exclusive(v_a_2791_)) as u8;
                        if v_isSharedCheck_3090_ == 0 {
                            v_unused_3091_ = crate::leanh::lean_ctor_get(v_a_2791_, 5);
                            crate::leanh::lean_dec(v_unused_3091_);
                            v_unused_3092_ = crate::leanh::lean_ctor_get(v_a_2791_, 4);
                            crate::leanh::lean_dec(v_unused_3092_);
                            v_unused_3093_ = crate::leanh::lean_ctor_get(v_a_2791_, 3);
                            crate::leanh::lean_dec(v_unused_3093_);
                            v_unused_3094_ = crate::leanh::lean_ctor_get(v_a_2791_, 2);
                            crate::leanh::lean_dec(v_unused_3094_);
                            v_unused_3095_ = crate::leanh::lean_ctor_get(v_a_2791_, 1);
                            crate::leanh::lean_dec(v_unused_3095_);
                            v_unused_3096_ = crate::leanh::lean_ctor_get(v_a_2791_, 0);
                            crate::leanh::lean_dec(v_unused_3096_);
                            v___x_3085_ = v_a_2791_;
                            v_isShared_3086_ = v_isSharedCheck_3090_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2791_);
                            v___x_3085_ = crate::leanh::lean_box(0);
                            v_isShared_3086_ = v_isSharedCheck_3090_;
                            state = 23;
                            continue;
                        }
                    } else {
                        v___y_3045_ = v___y_3074_;
                        v___y_3046_ = v___y_3075_;
                        v___y_3047_ = v___y_3076_;
                        v___y_3048_ = v___y_3077_;
                        v___y_3049_ = v___y_3078_;
                        v___y_3050_ = v___y_3079_;
                        v___y_3051_ = v___y_3083_;
                        v___y_3052_ = v___y_3080_;
                        v___y_3053_ = v___y_3081_;
                        v___y_3054_ = v___y_3082_;
                        v___y_3055_ = v_a_2790_;
                        v___y_3056_ = v_a_2791_;
                        state = 19;
                        continue;
                    }
                }
            }
            23 => {
                crate::leanh::lean_inc(v_totalJobs_2814_);
                crate::leanh::lean_inc(v_jobNo_2813_);
                if v_isShared_3086_ == 0 {
                    v___x_3088_ = v___x_3085_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3089_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_jobNo_2813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_totalJobs_2814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_failures_2816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_resetCtrl_2817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_lastUpdate_2818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 5, v_spinnerIdx_2819_);
                    v___x_3088_ = v_reuseFailAlloc_3089_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3088_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    v___y_3073_,
                );
                v___y_3045_ = v___y_3074_;
                v___y_3046_ = v___y_3075_;
                v___y_3047_ = v___y_3076_;
                v___y_3048_ = v___y_3077_;
                v___y_3049_ = v___y_3078_;
                v___y_3050_ = v___y_3079_;
                v___y_3051_ = v___y_3083_;
                v___y_3052_ = v___y_3080_;
                v___y_3053_ = v___y_3081_;
                v___y_3054_ = v___y_3082_;
                v___y_3055_ = v_a_2790_;
                v___y_3056_ = v___x_3088_;
                state = 19;
                continue;
            }
            25 => {
                v___x_3108_ = l_Lake_instOrdJobAction_ord(v_minAction_2823_, v___y_3100_);
                if v___x_3108_ == 2 {
                    v___x_3109_ = 0;
                    v___y_3073_ = v___y_3098_;
                    v___y_3074_ = v___y_3100_;
                    v___y_3075_ = v___y_3099_;
                    v___y_3076_ = v___y_3102_;
                    v___y_3077_ = v___y_3101_;
                    v___y_3078_ = v___y_3103_;
                    v___y_3079_ = v___y_3107_;
                    v___y_3080_ = v___y_3105_;
                    v___y_3081_ = v___y_3104_;
                    v___y_3082_ = v___y_3106_;
                    v___y_3083_ = v___x_3109_;
                    state = 22;
                    continue;
                } else {
                    v___x_3110_ = 1;
                    v___y_3073_ = v___y_3098_;
                    v___y_3074_ = v___y_3100_;
                    v___y_3075_ = v___y_3099_;
                    v___y_3076_ = v___y_3102_;
                    v___y_3077_ = v___y_3101_;
                    v___y_3078_ = v___y_3103_;
                    v___y_3079_ = v___y_3107_;
                    v___y_3080_ = v___y_3105_;
                    v___y_3081_ = v___y_3104_;
                    v___y_3082_ = v___y_3106_;
                    v___y_3083_ = v___x_3110_;
                    state = 22;
                    continue;
                }
            }
            26 => {
                v___x_3121_ = lean_strict_and(v___y_3118_, v___y_3120_);
                v___x_3122_ = l_Lake_instOrdLogLevel_ord(v_outLv_2821_, v___y_3119_);
                if v___x_3122_ == 2 {
                    v___x_3123_ = 0;
                    v___y_3098_ = v___y_3112_;
                    v___y_3099_ = v___y_3114_;
                    v___y_3100_ = v___y_3113_;
                    v___y_3101_ = v___y_3115_;
                    v___y_3102_ = v___x_3121_;
                    v___y_3103_ = v___y_3116_;
                    v___y_3104_ = v___y_3118_;
                    v___y_3105_ = v___y_3117_;
                    v___y_3106_ = v___y_3119_;
                    v___y_3107_ = v___x_3123_;
                    state = 25;
                    continue;
                } else {
                    v___x_3124_ = 1;
                    v___y_3098_ = v___y_3112_;
                    v___y_3099_ = v___y_3114_;
                    v___y_3100_ = v___y_3113_;
                    v___y_3101_ = v___y_3115_;
                    v___y_3102_ = v___x_3121_;
                    v___y_3103_ = v___y_3116_;
                    v___y_3104_ = v___y_3118_;
                    v___y_3105_ = v___y_3117_;
                    v___y_3106_ = v___y_3119_;
                    v___y_3107_ = v___x_3124_;
                    state = 25;
                    continue;
                }
            }
            27 => {
                v___x_3134_ = l_Lake_instOrdLogLevel_ord(v_failLv_2822_, v___y_3132_);
                if v___x_3134_ == 2 {
                    v___x_3135_ = 0;
                    v___y_3112_ = v___y_3126_;
                    v___y_3113_ = v___y_3128_;
                    v___y_3114_ = v___y_3127_;
                    v___y_3115_ = v___y_3129_;
                    v___y_3116_ = v___y_3130_;
                    v___y_3117_ = v___y_3131_;
                    v___y_3118_ = v___y_3133_;
                    v___y_3119_ = v___y_3132_;
                    v___y_3120_ = v___x_3135_;
                    state = 26;
                    continue;
                } else {
                    v___x_3136_ = 1;
                    v___y_3112_ = v___y_3126_;
                    v___y_3113_ = v___y_3128_;
                    v___y_3114_ = v___y_3127_;
                    v___y_3115_ = v___y_3129_;
                    v___y_3116_ = v___y_3130_;
                    v___y_3117_ = v___y_3131_;
                    v___y_3118_ = v___y_3133_;
                    v___y_3119_ = v___y_3132_;
                    v___y_3120_ = v___x_3136_;
                    state = 26;
                    continue;
                }
            }
            28 => {
                v_log_3139_ = crate::leanh::lean_ctor_get(v___y_3138_, 0);
                crate::leanh::lean_inc_ref(v_log_3139_);
                v_action_3140_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3138_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3141_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3138_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_3142_ = crate::leanh::lean_ctor_get(v___y_3138_, 2);
                crate::leanh::lean_inc(v_buildTime_3142_);
                crate::leanh::lean_dec_ref(v___y_3138_);
                v___x_3143_ = l_Lake_Log_maxLv(v_log_3139_);
                v___x_3144_ = lean_array_get_size(v_log_3139_);
                v___x_3145_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3146_ = lean_nat_dec_eq(v___x_3144_, v___x_3145_);
                if v___x_3146_ == 0 {
                    v___x_3147_ = 1;
                    v___y_3126_ = v_wantsRebuild_3141_;
                    v___y_3127_ = v___x_3144_;
                    v___y_3128_ = v_action_3140_;
                    v___y_3129_ = v_buildTime_3142_;
                    v___y_3130_ = v_log_3139_;
                    v___y_3131_ = v___x_3145_;
                    v___y_3132_ = v___x_3143_;
                    v___y_3133_ = v___x_3147_;
                    state = 27;
                    continue;
                } else {
                    v___x_3148_ = 0;
                    v___y_3126_ = v_wantsRebuild_3141_;
                    v___y_3127_ = v___x_3144_;
                    v___y_3128_ = v_action_3140_;
                    v___y_3129_ = v_buildTime_3142_;
                    v___y_3130_ = v_log_3139_;
                    v___y_3131_ = v___x_3145_;
                    v___y_3132_ = v___x_3143_;
                    v___y_3133_ = v___x_3148_;
                    state = 27;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___boxed(
    mut v_job_3151_: *mut crate::leanh::LeanObject,
    mut v_a_3152_: *mut crate::leanh::LeanObject,
    mut v_a_3153_: *mut crate::leanh::LeanObject,
    mut v_a_3154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3155_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(v_job_3151_, v_a_3152_, v_a_3153_);
    crate::leanh::lean_dec_ref(v_a_3152_);
    return v_res_3155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(
    mut v_out_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: u8,
    mut v_useAnsi_3158_: u8,
    mut v_as_3159_: *mut crate::leanh::LeanObject,
    mut v_i_3160_: usize,
    mut v_stop_3161_: usize,
    mut v_b_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___redArg(v_out_3156_, v___y_3157_, v_useAnsi_3158_, v_as_3159_, v_i_3160_, v_stop_3161_, v_b_3162_, v___y_3164_);
    return v___x_3166_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0___boxed(
    mut v_out_3167_: *mut crate::leanh::LeanObject,
    mut v___y_3168_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_3169_: *mut crate::leanh::LeanObject,
    mut v_as_3170_: *mut crate::leanh::LeanObject,
    mut v_i_3171_: *mut crate::leanh::LeanObject,
    mut v_stop_3172_: *mut crate::leanh::LeanObject,
    mut v_b_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_17198__boxed_3177_: u8 = 0;
    let mut v_useAnsi_17199__boxed_3178_: u8 = 0;
    let mut v_i_boxed_3179_: usize = 0;
    let mut v_stop_boxed_3180_: usize = 0;
    let mut v_res_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_17198__boxed_3177_ = (crate::leanh::lean_unbox(v___y_3168_) as u8);
    v_useAnsi_17199__boxed_3178_ = (crate::leanh::lean_unbox(v_useAnsi_3169_) as u8);
    v_i_boxed_3179_ = crate::leanh::lean_unbox_usize(v_i_3171_);
    crate::leanh::lean_dec(v_i_3171_);
    v_stop_boxed_3180_ = crate::leanh::lean_unbox_usize(v_stop_3172_);
    crate::leanh::lean_dec(v_stop_3172_);
    v_res_3181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_reportJob_spec__0(v_out_3167_, v___y_17198__boxed_3177_, v_useAnsi_17199__boxed_3178_, v_as_3170_, v_i_boxed_3179_, v_stop_boxed_3180_, v_b_3173_, v___y_3174_, v___y_3175_);
    crate::leanh::lean_dec_ref(v___y_3174_);
    crate::leanh::lean_dec_ref(v_as_3170_);
    return v_res_3181_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_jobs_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jobNo_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalJobs_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_3191_: u8 = 0;
    let mut v_failures_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resetCtrl_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUpdate_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spinnerIdx_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_jobs_3185_ = crate::leanh::lean_ctor_get(v_a_3182_, 0);
                v___x_3186_ = lean_st_ref_take(v_jobs_3185_);
                v___x_3187_ = l_Lake_mkBuildContext___closed__0;
                v___x_3188_ = lean_st_ref_set(v_jobs_3185_, v___x_3187_);
                v_jobNo_3189_ = crate::leanh::lean_ctor_get(v_a_3183_, 0);
                v_totalJobs_3190_ = crate::leanh::lean_ctor_get(v_a_3183_, 1);
                v_wantsRebuild_3191_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3183_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_failures_3192_ = crate::leanh::lean_ctor_get(v_a_3183_, 2);
                v_resetCtrl_3193_ = crate::leanh::lean_ctor_get(v_a_3183_, 3);
                v_lastUpdate_3194_ = crate::leanh::lean_ctor_get(v_a_3183_, 4);
                v_spinnerIdx_3195_ = crate::leanh::lean_ctor_get(v_a_3183_, 5);
                v_isSharedCheck_3205_ = (!crate::leanh::lean_is_exclusive(v_a_3183_)) as u8;
                if v_isSharedCheck_3205_ == 0 {
                    v___x_3197_ = v_a_3183_;
                    v_isShared_3198_ = v_isSharedCheck_3205_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_spinnerIdx_3195_);
                    crate::leanh::lean_inc(v_lastUpdate_3194_);
                    crate::leanh::lean_inc(v_resetCtrl_3193_);
                    crate::leanh::lean_inc(v_failures_3192_);
                    crate::leanh::lean_inc(v_totalJobs_3190_);
                    crate::leanh::lean_inc(v_jobNo_3189_);
                    crate::leanh::lean_dec(v_a_3183_);
                    v___x_3197_ = crate::leanh::lean_box(0);
                    v_isShared_3198_ = v_isSharedCheck_3205_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3199_ = lean_array_get_size(v___x_3186_);
                v___x_3200_ = lean_nat_add(v_totalJobs_3190_, v___x_3199_);
                crate::leanh::lean_dec(v_totalJobs_3190_);
                if v_isShared_3198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3197_, 1, v___x_3200_);
                    v___x_3202_ = v___x_3197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_jobNo_3189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___x_3200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 2, v_failures_3192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 3, v_resetCtrl_3193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 4, v_lastUpdate_3194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 5, v_spinnerIdx_3195_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3204_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        v_wantsRebuild_3191_,
                    );
                    v___x_3202_ = v_reuseFailAlloc_3204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3203_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3203_, 0, v___x_3186_);
                crate::leanh::lean_ctor_set(v___x_3203_, 1, v___x_3202_);
                return v___x_3203_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue___boxed(
    mut v_a_3206_: *mut crate::leanh::LeanObject,
    mut v_a_3207_: *mut crate::leanh::LeanObject,
    mut v_a_3208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3209_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_3206_, v_a_3207_);
    crate::leanh::lean_dec_ref(v_a_3206_);
    return v_res_3209_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(
    mut v_as_3210_: *mut crate::leanh::LeanObject,
    mut v_i_3211_: usize,
    mut v_stop_3212_: usize,
    mut v_b_3213_: *mut crate::leanh::LeanObject,
    mut v___y_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: usize = 0;
    let mut v___x_3221_: usize = 0;
    let mut v___x_3223_: u8 = 0;
    let mut v_fst_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: u8 = 0;
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3231_: u8 = 0;
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_unused_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3241_: u8 = 0;
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v_unused_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jobNo_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalJobs_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_3254_: u8 = 0;
    let mut v_failures_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resetCtrl_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUpdate_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spinnerIdx_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3223_ = lean_usize_dec_eq(v_i_3211_, v_stop_3212_);
                if v___x_3223_ == 0 {
                    v_fst_3224_ = crate::leanh::lean_ctor_get(v_b_3213_, 0);
                    v_snd_3225_ = crate::leanh::lean_ctor_get(v_b_3213_, 1);
                    v___x_3226_ = lean_array_uget_borrowed(v_as_3210_, v_i_3211_);
                    v_task_3227_ = crate::leanh::lean_ctor_get(v___x_3226_, 0);
                    v___x_3228_ = lean_io_get_task_state(v_task_3227_);
                    match v___x_3228_ {
                        0 => {
                            crate::leanh::lean_inc(v_snd_3225_);
                            crate::leanh::lean_inc(v_fst_3224_);
                            v_isSharedCheck_3236_ =
                                (!crate::leanh::lean_is_exclusive(v_b_3213_)) as u8;
                            if v_isSharedCheck_3236_ == 0 {
                                v_unused_3237_ = crate::leanh::lean_ctor_get(v_b_3213_, 1);
                                crate::leanh::lean_dec(v_unused_3237_);
                                v_unused_3238_ = crate::leanh::lean_ctor_get(v_b_3213_, 0);
                                crate::leanh::lean_dec(v_unused_3238_);
                                v___x_3230_ = v_b_3213_;
                                v_isShared_3231_ = v_isSharedCheck_3236_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_b_3213_);
                                v___x_3230_ = crate::leanh::lean_box(0);
                                v_isShared_3231_ = v_isSharedCheck_3236_;
                                state = 2;
                                continue;
                            }
                        }
                        1 => {
                            crate::leanh::lean_inc(v_snd_3225_);
                            crate::leanh::lean_inc(v_fst_3224_);
                            v_isSharedCheck_3247_ =
                                (!crate::leanh::lean_is_exclusive(v_b_3213_)) as u8;
                            if v_isSharedCheck_3247_ == 0 {
                                v_unused_3248_ = crate::leanh::lean_ctor_get(v_b_3213_, 1);
                                crate::leanh::lean_dec(v_unused_3248_);
                                v_unused_3249_ = crate::leanh::lean_ctor_get(v_b_3213_, 0);
                                crate::leanh::lean_dec(v_unused_3249_);
                                v___x_3240_ = v_b_3213_;
                                v_isShared_3241_ = v_isSharedCheck_3247_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_b_3213_);
                                v___x_3240_ = crate::leanh::lean_box(0);
                                v_isShared_3241_ = v_isSharedCheck_3247_;
                                state = 4;
                                continue;
                            }
                        }
                        _ => {
                            crate::leanh::lean_inc(v___x_3226_);
                            v___x_3250_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob(
                                v___x_3226_,
                                v___y_3214_,
                                v___y_3215_,
                            );
                            v_snd_3251_ = crate::leanh::lean_ctor_get(v___x_3250_, 1);
                            crate::leanh::lean_inc(v_snd_3251_);
                            crate::leanh::lean_dec_ref(v___x_3250_);
                            v_jobNo_3252_ = crate::leanh::lean_ctor_get(v_snd_3251_, 0);
                            v_totalJobs_3253_ = crate::leanh::lean_ctor_get(v_snd_3251_, 1);
                            v_wantsRebuild_3254_ = crate::leanh::lean_ctor_get_uint8(
                                v_snd_3251_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                            );
                            v_failures_3255_ = crate::leanh::lean_ctor_get(v_snd_3251_, 2);
                            v_resetCtrl_3256_ = crate::leanh::lean_ctor_get(v_snd_3251_, 3);
                            v_lastUpdate_3257_ = crate::leanh::lean_ctor_get(v_snd_3251_, 4);
                            v_spinnerIdx_3258_ = crate::leanh::lean_ctor_get(v_snd_3251_, 5);
                            v_isSharedCheck_3267_ =
                                (!crate::leanh::lean_is_exclusive(v_snd_3251_)) as u8;
                            if v_isSharedCheck_3267_ == 0 {
                                v___x_3260_ = v_snd_3251_;
                                v_isShared_3261_ = v_isSharedCheck_3267_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_spinnerIdx_3258_);
                                crate::leanh::lean_inc(v_lastUpdate_3257_);
                                crate::leanh::lean_inc(v_resetCtrl_3256_);
                                crate::leanh::lean_inc(v_failures_3255_);
                                crate::leanh::lean_inc(v_totalJobs_3253_);
                                crate::leanh::lean_inc(v_jobNo_3252_);
                                crate::leanh::lean_dec(v_snd_3251_);
                                v___x_3260_ = crate::leanh::lean_box(0);
                                v_isShared_3261_ = v_isSharedCheck_3267_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_3268_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3268_, 0, v_b_3213_);
                    crate::leanh::lean_ctor_set(v___x_3268_, 1, v___y_3215_);
                    return v___x_3268_;
                }
            }
            1 => {
                v___x_3220_ = 1usize;
                v___x_3221_ = lean_usize_add(v_i_3211_, v___x_3220_);
                v_i_3211_ = v___x_3221_;
                v_b_3213_ = v_fst_3218_;
                v___y_3215_ = v_snd_3219_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v___x_3226_);
                v___x_3232_ = lean_array_push(v_snd_3225_, v___x_3226_);
                if v_isShared_3231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3230_, 1, v___x_3232_);
                    v___x_3234_ = v___x_3230_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_fst_3224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 1, v___x_3232_);
                    v___x_3234_ = v_reuseFailAlloc_3235_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_3218_ = v___x_3234_;
                v_snd_3219_ = v___y_3215_;
                state = 1;
                continue;
            }
            4 => {
                crate::leanh::lean_inc_n(v___x_3226_, 2);
                v___x_3242_ = lean_array_push(v_fst_3224_, v___x_3226_);
                v___x_3243_ = lean_array_push(v_snd_3225_, v___x_3226_);
                if v_isShared_3241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3240_, 1, v___x_3243_);
                    crate::leanh::lean_ctor_set(v___x_3240_, 0, v___x_3242_);
                    v___x_3245_ = v___x_3240_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 1, v___x_3243_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_3218_ = v___x_3245_;
                v_snd_3219_ = v___y_3215_;
                state = 1;
                continue;
            }
            6 => {
                v___x_3262_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3263_ = lean_nat_add(v_jobNo_3252_, v___x_3262_);
                crate::leanh::lean_dec(v_jobNo_3252_);
                if v_isShared_3261_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3263_);
                    v___x_3265_ = v___x_3260_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3266_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_totalJobs_3253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_failures_3255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 3, v_resetCtrl_3256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 4, v_lastUpdate_3257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 5, v_spinnerIdx_3258_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3266_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        v_wantsRebuild_3254_,
                    );
                    v___x_3265_ = v_reuseFailAlloc_3266_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_3218_ = v_b_3213_;
                v_snd_3219_ = v___x_3265_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0___boxed(
    mut v_as_3269_: *mut crate::leanh::LeanObject,
    mut v_i_3270_: *mut crate::leanh::LeanObject,
    mut v_stop_3271_: *mut crate::leanh::LeanObject,
    mut v_b_3272_: *mut crate::leanh::LeanObject,
    mut v___y_3273_: *mut crate::leanh::LeanObject,
    mut v___y_3274_: *mut crate::leanh::LeanObject,
    mut v___y_3275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3276_: usize = 0;
    let mut v_stop_boxed_3277_: usize = 0;
    let mut v_res_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3276_ = crate::leanh::lean_unbox_usize(v_i_3270_);
    crate::leanh::lean_dec(v_i_3270_);
    v_stop_boxed_3277_ = crate::leanh::lean_unbox_usize(v_stop_3271_);
    crate::leanh::lean_dec(v_stop_3271_);
    v_res_3278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_as_3269_, v_i_boxed_3276_, v_stop_boxed_3277_, v_b_3272_, v___y_3273_, v___y_3274_);
    crate::leanh::lean_dec_ref(v___y_3273_);
    crate::leanh::lean_dec_ref(v_as_3269_);
    return v_res_3278_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(
    mut v_new_3281_: *mut crate::leanh::LeanObject,
    mut v_unfinished_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_a_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: u8 = 0;
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: usize = 0;
    let mut v___x_3295_: usize = 0;
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: usize = 0;
    let mut v___x_3298_: usize = 0;
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: u8 = 0;
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: u8 = 0;
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: usize = 0;
    let mut v___x_3311_: usize = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: usize = 0;
    let mut v___x_3314_: usize = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3286_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3304_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___closed__0;
                v___x_3305_ = lean_array_get_size(v_unfinished_3282_);
                v___x_3306_ = lean_nat_dec_lt(v___x_3286_, v___x_3305_);
                if v___x_3306_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3284_);
                    v___x_3307_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3307_, 0, v___x_3304_);
                    crate::leanh::lean_ctor_set(v___x_3307_, 1, v_a_3284_);
                    v___y_3288_ = v___x_3307_;
                    v_fst_3289_ = v___x_3304_;
                    v_snd_3290_ = v_a_3284_;
                    state = 1;
                    continue;
                } else {
                    v___x_3308_ = lean_nat_dec_le(v___x_3305_, v___x_3305_);
                    if v___x_3308_ == 0 {
                        if v___x_3306_ == 0 {
                            crate::leanh::lean_inc_ref(v_a_3284_);
                            v___x_3309_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3309_, 0, v___x_3304_);
                            crate::leanh::lean_ctor_set(v___x_3309_, 1, v_a_3284_);
                            v___y_3288_ = v___x_3309_;
                            v_fst_3289_ = v___x_3304_;
                            v_snd_3290_ = v_a_3284_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3310_ = 0usize;
                            v___x_3311_ = lean_usize_of_nat(v___x_3305_);
                            v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_3282_, v___x_3310_, v___x_3311_, v___x_3304_, v_a_3283_, v_a_3284_);
                            v___y_3301_ = v___x_3312_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_3313_ = 0usize;
                        v___x_3314_ = lean_usize_of_nat(v___x_3305_);
                        v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_unfinished_3282_, v___x_3313_, v___x_3314_, v___x_3304_, v_a_3283_, v_a_3284_);
                        v___y_3301_ = v___x_3315_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3291_ = lean_array_get_size(v_new_3281_);
                v___x_3292_ = lean_nat_dec_lt(v___x_3286_, v___x_3291_);
                if v___x_3292_ == 0 {
                    crate::leanh::lean_dec_ref(v_snd_3290_);
                    crate::leanh::lean_dec_ref(v_fst_3289_);
                    return v___y_3288_;
                } else {
                    v___x_3293_ = lean_nat_dec_le(v___x_3291_, v___x_3291_);
                    if v___x_3293_ == 0 {
                        if v___x_3292_ == 0 {
                            crate::leanh::lean_dec_ref(v_snd_3290_);
                            crate::leanh::lean_dec_ref(v_fst_3289_);
                            return v___y_3288_;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_3288_);
                            v___x_3294_ = 0usize;
                            v___x_3295_ = lean_usize_of_nat(v___x_3291_);
                            v___x_3296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_3281_, v___x_3294_, v___x_3295_, v_fst_3289_, v_a_3283_, v_snd_3290_);
                            return v___x_3296_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3288_);
                        v___x_3297_ = 0usize;
                        v___x_3298_ = lean_usize_of_nat(v___x_3291_);
                        v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Monitor_scanJobs_spec__0(v_new_3281_, v___x_3297_, v___x_3298_, v_fst_3289_, v_a_3283_, v_snd_3290_);
                        return v___x_3299_;
                    }
                }
            }
            2 => {
                v_fst_3302_ = crate::leanh::lean_ctor_get(v___y_3301_, 0);
                crate::leanh::lean_inc(v_fst_3302_);
                v_snd_3303_ = crate::leanh::lean_ctor_get(v___y_3301_, 1);
                crate::leanh::lean_inc(v_snd_3303_);
                v___y_3288_ = v___y_3301_;
                v_fst_3289_ = v_fst_3302_;
                v_snd_3290_ = v_snd_3303_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs___boxed(
    mut v_new_3316_: *mut crate::leanh::LeanObject,
    mut v_unfinished_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
    mut v_a_3319_: *mut crate::leanh::LeanObject,
    mut v_a_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3321_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(
        v_new_3316_,
        v_unfinished_3317_,
        v_a_3318_,
        v_a_3319_,
    );
    crate::leanh::lean_dec_ref(v_a_3318_);
    crate::leanh::lean_dec_ref(v_unfinished_3317_);
    crate::leanh::lean_dec_ref(v_new_3316_);
    return v_res_3321_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_sleep(
    mut v_a_3322_: *mut crate::leanh::LeanObject,
    mut v_a_3323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_jobNo_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalJobs_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_3330_: u8 = 0;
    let mut v_failures_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resetCtrl_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spinnerIdx_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3342_: u8 = 0;
    let mut v_unused_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUpdate_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_updateFrequency_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: u8 = 0;
    let mut v___x_3351_: u32 = 0;
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3344_ = lean_io_mono_ms_now();
                v_lastUpdate_3345_ = crate::leanh::lean_ctor_get(v_a_3323_, 4);
                v_updateFrequency_3346_ = crate::leanh::lean_ctor_get(v_a_3322_, 2);
                v___x_3347_ = lean_nat_sub(v___x_3344_, v_lastUpdate_3345_);
                crate::leanh::lean_dec(v___x_3344_);
                v___x_3348_ = lean_nat_sub(v_updateFrequency_3346_, v___x_3347_);
                crate::leanh::lean_dec(v___x_3347_);
                v___x_3349_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3350_ = lean_nat_dec_lt(v___x_3349_, v___x_3348_);
                if v___x_3350_ == 0 {
                    crate::leanh::lean_dec(v___x_3348_);
                    v___y_3326_ = v_a_3323_;
                    state = 1;
                    continue;
                } else {
                    v___x_3351_ = lean_uint32_of_nat(v___x_3348_);
                    crate::leanh::lean_dec(v___x_3348_);
                    v___x_3352_ = l_IO_sleep(v___x_3351_);
                    v___y_3326_ = v_a_3323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3327_ = lean_io_mono_ms_now();
                v_jobNo_3328_ = crate::leanh::lean_ctor_get(v___y_3326_, 0);
                v_totalJobs_3329_ = crate::leanh::lean_ctor_get(v___y_3326_, 1);
                v_wantsRebuild_3330_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3326_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_failures_3331_ = crate::leanh::lean_ctor_get(v___y_3326_, 2);
                v_resetCtrl_3332_ = crate::leanh::lean_ctor_get(v___y_3326_, 3);
                v_spinnerIdx_3333_ = crate::leanh::lean_ctor_get(v___y_3326_, 5);
                v_isSharedCheck_3342_ = (!crate::leanh::lean_is_exclusive(v___y_3326_)) as u8;
                if v_isSharedCheck_3342_ == 0 {
                    v_unused_3343_ = crate::leanh::lean_ctor_get(v___y_3326_, 4);
                    crate::leanh::lean_dec(v_unused_3343_);
                    v___x_3335_ = v___y_3326_;
                    v_isShared_3336_ = v_isSharedCheck_3342_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_spinnerIdx_3333_);
                    crate::leanh::lean_inc(v_resetCtrl_3332_);
                    crate::leanh::lean_inc(v_failures_3331_);
                    crate::leanh::lean_inc(v_totalJobs_3329_);
                    crate::leanh::lean_inc(v_jobNo_3328_);
                    crate::leanh::lean_dec(v___y_3326_);
                    v___x_3335_ = crate::leanh::lean_box(0);
                    v_isShared_3336_ = v_isSharedCheck_3342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3337_ = crate::leanh::lean_box(0);
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v___x_3327_);
                    v___x_3339_ = v___x_3335_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3341_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_jobNo_3328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_totalJobs_3329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 2, v_failures_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 3, v_resetCtrl_3332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 4, v___x_3327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 5, v_spinnerIdx_3333_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3341_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        v_wantsRebuild_3330_,
                    );
                    v___x_3339_ = v_reuseFailAlloc_3341_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3340_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3340_, 0, v___x_3337_);
                crate::leanh::lean_ctor_set(v___x_3340_, 1, v___x_3339_);
                return v___x_3340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_sleep___boxed(
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3356_ = l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_3353_, v_a_3354_);
    crate::leanh::lean_dec_ref(v_a_3353_);
    return v_res_3356_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_loop(
    mut v_new_3357_: *mut crate::leanh::LeanObject,
    mut v_unfinished_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
    mut v_a_3360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: u8 = 0;
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3375_: u8 = 0;
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: u8 = 0;
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3362_ = l___private_Lake_Build_Run_0__Lake_Monitor_scanJobs(
                    v_new_3357_,
                    v_unfinished_3358_,
                    v_a_3359_,
                    v_a_3360_,
                );
                crate::leanh::lean_dec_ref(v_unfinished_3358_);
                crate::leanh::lean_dec_ref(v_new_3357_);
                v_fst_3363_ = crate::leanh::lean_ctor_get(v___x_3362_, 0);
                crate::leanh::lean_inc(v_fst_3363_);
                v_snd_3364_ = crate::leanh::lean_ctor_get(v___x_3362_, 1);
                crate::leanh::lean_inc(v_snd_3364_);
                crate::leanh::lean_dec_ref(v___x_3362_);
                v_fst_3365_ = crate::leanh::lean_ctor_get(v_fst_3363_, 0);
                crate::leanh::lean_inc(v_fst_3365_);
                v_snd_3366_ = crate::leanh::lean_ctor_get(v_fst_3363_, 1);
                crate::leanh::lean_inc(v_snd_3366_);
                crate::leanh::lean_dec(v_fst_3363_);
                v___x_3367_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3368_ = lean_array_get_size(v_snd_3366_);
                v___x_3369_ = lean_nat_dec_lt(v___x_3367_, v___x_3368_);
                if v___x_3369_ == 0 {
                    crate::leanh::lean_dec(v_fst_3365_);
                    v___x_3370_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(
                        v_a_3359_,
                        v_snd_3364_,
                    );
                    v_fst_3371_ = crate::leanh::lean_ctor_get(v___x_3370_, 0);
                    v_snd_3372_ = crate::leanh::lean_ctor_get(v___x_3370_, 1);
                    v_isSharedCheck_3383_ = (!crate::leanh::lean_is_exclusive(v___x_3370_)) as u8;
                    if v_isSharedCheck_3383_ == 0 {
                        v___x_3374_ = v___x_3370_;
                        v_isShared_3375_ = v_isSharedCheck_3383_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3372_);
                        crate::leanh::lean_inc(v_fst_3371_);
                        crate::leanh::lean_dec(v___x_3370_);
                        v___x_3374_ = crate::leanh::lean_box(0);
                        v_isShared_3375_ = v_isSharedCheck_3383_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3384_ =
                        l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg(
                            v_fst_3365_,
                            v_snd_3366_,
                            v_a_3359_,
                            v_snd_3364_,
                        );
                    crate::leanh::lean_dec(v_fst_3365_);
                    v_snd_3385_ = crate::leanh::lean_ctor_get(v___x_3384_, 1);
                    crate::leanh::lean_inc(v_snd_3385_);
                    crate::leanh::lean_dec_ref(v___x_3384_);
                    v___x_3386_ =
                        l___private_Lake_Build_Run_0__Lake_Monitor_sleep(v_a_3359_, v_snd_3385_);
                    v_snd_3387_ = crate::leanh::lean_ctor_get(v___x_3386_, 1);
                    crate::leanh::lean_inc(v_snd_3387_);
                    crate::leanh::lean_dec_ref(v___x_3386_);
                    v___x_3388_ = l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(
                        v_a_3359_,
                        v_snd_3387_,
                    );
                    v_fst_3389_ = crate::leanh::lean_ctor_get(v___x_3388_, 0);
                    crate::leanh::lean_inc(v_fst_3389_);
                    v_snd_3390_ = crate::leanh::lean_ctor_get(v___x_3388_, 1);
                    crate::leanh::lean_inc(v_snd_3390_);
                    crate::leanh::lean_dec_ref(v___x_3388_);
                    v_new_3357_ = v_fst_3389_;
                    v_unfinished_3358_ = v_snd_3366_;
                    v_a_3360_ = v_snd_3390_;
                    state = 0;
                    continue;
                }
            }
            1 => {
                v___x_3376_ = lean_array_get_size(v_fst_3371_);
                v___x_3377_ = lean_nat_dec_lt(v___x_3367_, v___x_3376_);
                if v___x_3377_ == 0 {
                    crate::leanh::lean_dec(v_fst_3371_);
                    crate::leanh::lean_dec(v_snd_3366_);
                    v___x_3378_ = crate::leanh::lean_box(0);
                    if v_isShared_3375_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3374_, 0, v___x_3378_);
                        v___x_3380_ = v___x_3374_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3381_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_snd_3372_);
                        v___x_3380_ = v_reuseFailAlloc_3381_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3374_);
                    v_new_3357_ = v_fst_3371_;
                    v_unfinished_3358_ = v_snd_3366_;
                    v_a_3360_ = v_snd_3372_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_3380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_loop___boxed(
    mut v_new_3392_: *mut crate::leanh::LeanObject,
    mut v_unfinished_3393_: *mut crate::leanh::LeanObject,
    mut v_a_3394_: *mut crate::leanh::LeanObject,
    mut v_a_3395_: *mut crate::leanh::LeanObject,
    mut v_a_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3397_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(
        v_new_3392_,
        v_unfinished_3393_,
        v_a_3394_,
        v_a_3395_,
    );
    crate::leanh::lean_dec_ref(v_a_3394_);
    return v_res_3397_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_main(
    mut v_init_3398_: *mut crate::leanh::LeanObject,
    mut v_a_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3407_: u8 = 0;
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3412_: u8 = 0;
    let mut v_jobNo_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalJobs_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_3415_: u8 = 0;
    let mut v_failures_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resetCtrl_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUpdate_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spinnerIdx_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: u8 = 0;
    let mut v_out_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3445_: u8 = 0;
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3464_: u8 = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3470_: u8 = 0;
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v_unused_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3402_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_drainQueue(v_a_3399_, v_a_3400_);
                v_fst_3403_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                v_snd_3404_ = crate::leanh::lean_ctor_get(v___x_3402_, 1);
                v_isSharedCheck_3473_ = (!crate::leanh::lean_is_exclusive(v___x_3402_)) as u8;
                if v_isSharedCheck_3473_ == 0 {
                    v___x_3406_ = v___x_3402_;
                    v_isShared_3407_ = v_isSharedCheck_3473_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3404_);
                    crate::leanh::lean_inc(v_fst_3403_);
                    crate::leanh::lean_dec(v___x_3402_);
                    v___x_3406_ = crate::leanh::lean_box(0);
                    v_isShared_3407_ = v_isSharedCheck_3473_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3408_ = l___private_Lake_Build_Run_0__Lake_Monitor_loop(
                    v_fst_3403_,
                    v_init_3398_,
                    v_a_3399_,
                    v_snd_3404_,
                );
                v_snd_3409_ = crate::leanh::lean_ctor_get(v___x_3408_, 1);
                v_isSharedCheck_3471_ = (!crate::leanh::lean_is_exclusive(v___x_3408_)) as u8;
                if v_isSharedCheck_3471_ == 0 {
                    v_unused_3472_ = crate::leanh::lean_ctor_get(v___x_3408_, 0);
                    crate::leanh::lean_dec(v_unused_3472_);
                    v___x_3411_ = v___x_3408_;
                    v_isShared_3412_ = v_isSharedCheck_3471_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3409_);
                    crate::leanh::lean_dec(v___x_3408_);
                    v___x_3411_ = crate::leanh::lean_box(0);
                    v_isShared_3412_ = v_isSharedCheck_3471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_jobNo_3413_ = crate::leanh::lean_ctor_get(v_snd_3409_, 0);
                v_totalJobs_3414_ = crate::leanh::lean_ctor_get(v_snd_3409_, 1);
                v_wantsRebuild_3415_ = crate::leanh::lean_ctor_get_uint8(
                    v_snd_3409_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                );
                v_failures_3416_ = crate::leanh::lean_ctor_get(v_snd_3409_, 2);
                v_resetCtrl_3417_ = crate::leanh::lean_ctor_get(v_snd_3409_, 3);
                v_lastUpdate_3418_ = crate::leanh::lean_ctor_get(v_snd_3409_, 4);
                v_spinnerIdx_3419_ = crate::leanh::lean_ctor_get(v_snd_3409_, 5);
                v_isSharedCheck_3470_ = (!crate::leanh::lean_is_exclusive(v_snd_3409_)) as u8;
                if v_isSharedCheck_3470_ == 0 {
                    v___x_3421_ = v_snd_3409_;
                    v_isShared_3422_ = v_isSharedCheck_3470_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_spinnerIdx_3419_);
                    crate::leanh::lean_inc(v_lastUpdate_3418_);
                    crate::leanh::lean_inc(v_resetCtrl_3417_);
                    crate::leanh::lean_inc(v_failures_3416_);
                    crate::leanh::lean_inc(v_totalJobs_3414_);
                    crate::leanh::lean_inc(v_jobNo_3413_);
                    crate::leanh::lean_dec(v_snd_3409_);
                    v___x_3421_ = crate::leanh::lean_box(0);
                    v_isShared_3422_ = v_isSharedCheck_3470_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3423_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
                if v_isShared_3422_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3421_, 3, v___x_3423_);
                    v___x_3425_ = v___x_3421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_jobNo_3413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_totalJobs_3414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_failures_3416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 3, v___x_3423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_lastUpdate_3418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 5, v_spinnerIdx_3419_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3469_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                        v_wantsRebuild_3415_,
                    );
                    v___x_3425_ = v_reuseFailAlloc_3469_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3431_ = lean_string_utf8_byte_size(v_resetCtrl_3417_);
                v___x_3432_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3433_ = lean_nat_dec_eq(v___x_3431_, v___x_3432_);
                if v___x_3433_ == 0 {
                    crate::leanh::lean_del_object(v___x_3406_);
                    v_out_3434_ = crate::leanh::lean_ctor_get(v_a_3399_, 1);
                    v_flush_3435_ = crate::leanh::lean_ctor_get(v_out_3434_, 0);
                    v_putStr_3436_ = crate::leanh::lean_ctor_get(v_out_3434_, 4);
                    crate::leanh::lean_inc_ref(v_putStr_3436_);
                    crate::leanh::lean_inc_ref(v_resetCtrl_3417_);
                    v___x_3441_ = crate::leanh::lean_apply_2(
                        v_putStr_3436_,
                        v_resetCtrl_3417_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3441_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3441_, 1);
                        crate::leanh::lean_dec_ref(v_resetCtrl_3417_);
                        state = 7;
                        continue;
                    } else {
                        v_a_3442_ = crate::leanh::lean_ctor_get(v___x_3441_, 0);
                        v_isSharedCheck_3464_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3441_)) as u8;
                        if v_isSharedCheck_3464_ == 0 {
                            v___x_3444_ = v___x_3441_;
                            v_isShared_3445_ = v_isSharedCheck_3464_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3442_);
                            crate::leanh::lean_dec(v___x_3441_);
                            v___x_3444_ = crate::leanh::lean_box(0);
                            v_isShared_3445_ = v_isSharedCheck_3464_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_resetCtrl_3417_);
                    crate::leanh::lean_del_object(v___x_3411_);
                    v___x_3465_ = crate::leanh::lean_box(0);
                    if v_isShared_3407_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3406_, 1, v___x_3425_);
                        crate::leanh::lean_ctor_set(v___x_3406_, 0, v___x_3465_);
                        v___x_3467_ = v___x_3406_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3468_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3425_);
                        v___x_3467_ = v_reuseFailAlloc_3468_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3412_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3411_, 1, v___x_3425_);
                    crate::leanh::lean_ctor_set(v___x_3411_, 0, v_val_3427_);
                    v___x_3429_ = v___x_3411_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_val_3427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 1, v___x_3425_);
                    v___x_3429_ = v_reuseFailAlloc_3430_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3429_;
            }
            7 => {
                crate::leanh::lean_inc_ref(v_flush_3435_);
                v___x_3438_ = crate::leanh::lean_apply_1(v_flush_3435_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_3438_) == 0 {
                    v_a_3439_ = crate::leanh::lean_ctor_get(v___x_3438_, 0);
                    crate::leanh::lean_inc(v_a_3439_);
                    crate::leanh::lean_dec_ref_known(v___x_3438_, 1);
                    v_val_3427_ = v_a_3439_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3438_, 1);
                    v___x_3440_ = crate::leanh::lean_box(0);
                    v_val_3427_ = v___x_3440_;
                    state = 5;
                    continue;
                }
            }
            8 => {
                v___x_3446_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                v___x_3447_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                v___x_3448_ = crate::leanh::lean_unsigned_to_nat(89);
                v___x_3449_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3450_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once
                    ),
                    _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19,
                );
                v___x_3451_ = lean_io_error_to_string(v_a_3442_);
                v___x_3452_ = lean_string_append(v___x_3450_, v___x_3451_);
                crate::leanh::lean_dec_ref(v___x_3451_);
                v___x_3453_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                v___x_3454_ = lean_string_append(v___x_3452_, v___x_3453_);
                v___x_3455_ = l_String_quote(v_resetCtrl_3417_);
                if v_isShared_3445_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3444_, 3);
                    crate::leanh::lean_ctor_set(v___x_3444_, 0, v___x_3455_);
                    v___x_3457_ = v___x_3444_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3463_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3455_);
                    v___x_3457_ = v_reuseFailAlloc_3463_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3458_ = l_Std_Format_defWidth;
                v___x_3459_ =
                    l_Std_Format_pretty(v___x_3457_, v___x_3458_, v___x_3432_, v___x_3432_);
                v___x_3460_ = lean_string_append(v___x_3454_, v___x_3459_);
                crate::leanh::lean_dec_ref(v___x_3459_);
                v___x_3461_ = l_mkPanicMessageWithDecl(
                    v___x_3446_,
                    v___x_3447_,
                    v___x_3448_,
                    v___x_3449_,
                    v___x_3460_,
                );
                crate::leanh::lean_dec_ref(v___x_3460_);
                v___x_3462_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_3461_);
                state = 7;
                continue;
            }
            10 => {
                return v___x_3467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Monitor_main___boxed(
    mut v_init_3474_: *mut crate::leanh::LeanObject,
    mut v_a_3475_: *mut crate::leanh::LeanObject,
    mut v_a_3476_: *mut crate::leanh::LeanObject,
    mut v_a_3477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3478_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_main(v_init_3474_, v_a_3475_, v_a_3476_);
    crate::leanh::lean_dec_ref(v_a_3475_);
    return v_res_3478_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(
    mut v_self_3479_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_failures_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: u8 = 0;
    v_failures_3480_ = crate::leanh::lean_ctor_get(v_self_3479_, 0);
    v___x_3481_ = lean_array_get_size(v_failures_3480_);
    v___x_3482_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3483_ = lean_nat_dec_eq(v___x_3481_, v___x_3482_);
    return v___x_3483_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk___boxed(
    mut v_self_3484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3485_: u8 = 0;
    let mut v_r_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3485_ = l___private_Lake_Build_Run_0__Lake_MonitorResult_isOk(v_self_3484_);
    crate::leanh::lean_dec_ref(v_self_3484_);
    v_r_3486_ = crate::leanh::lean_box((v_res_3485_) as usize);
    return v_r_3486_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_mkMonitorContext(
    mut v_cfg_3487_: *mut crate::leanh::LeanObject,
    mut v_jobs_3488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toLogConfig_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_verbosity_3491_: u8 = 0;
    let mut v_failLv_3492_: u8 = 0;
    let mut v_outLv_3493_: u8 = 0;
    let mut v_ansiMode_3494_: u8 = 0;
    let mut v_out_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: u8 = 0;
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: u8 = 0;
    let mut v___x_3500_: u8 = 0;
    let mut v___y_3502_: u8 = 0;
    let mut v___y_3503_: u8 = 0;
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3507_: u8 = 0;
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: u8 = 0;
    let mut v___x_3510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toLogConfig_3490_ = crate::leanh::lean_ctor_get(v_cfg_3487_, 0);
                v_verbosity_3491_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_3487_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_failLv_3492_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLogConfig_3490_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_outLv_3493_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLogConfig_3490_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_3494_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLogConfig_3490_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_3495_ = crate::leanh::lean_ctor_get(v_toLogConfig_3490_, 0);
                v___x_3496_ = l_Lake_OutStream_get(v_out_3495_);
                crate::leanh::lean_inc_ref(v___x_3496_);
                v___x_3497_ = l_Lake_AnsiMode_isEnabled(v___x_3496_, v_ansiMode_3494_);
                v___x_3498_ = l_Lake_BuildConfig_showProgress(v_cfg_3487_);
                v___x_3499_ = 2;
                v___x_3500_ = l_Lake_instDecidableEqVerbosity(v_verbosity_3491_, v___x_3499_);
                if v___x_3500_ == 0 {
                    v___x_3509_ = 3;
                    v___y_3507_ = v___x_3509_;
                    state = 2;
                    continue;
                } else {
                    v___x_3510_ = 0;
                    v___y_3507_ = v___x_3510_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3504_ = crate::leanh::lean_unsigned_to_nat(100);
                v___x_3505_ = crate::leanh::lean_alloc_ctor(0, 3, (7) as u32);
                crate::leanh::lean_ctor_set(v___x_3505_, 0, v_jobs_3488_);
                crate::leanh::lean_ctor_set(v___x_3505_, 1, v___x_3496_);
                crate::leanh::lean_ctor_set(v___x_3505_, 2, v___x_3504_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_outLv_3493_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v_failLv_3492_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                    v___y_3502_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                    v___x_3500_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                    v___x_3497_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                    v___x_3498_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3505_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
                    v___y_3503_,
                );
                return v___x_3505_;
            }
            2 => {
                if v___x_3500_ == 0 {
                    if v___x_3497_ == 0 {
                        v___x_3508_ = 1;
                        v___y_3502_ = v___y_3507_;
                        v___y_3503_ = v___x_3508_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3502_ = v___y_3507_;
                        v___y_3503_ = v___x_3500_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_3502_ = v___y_3507_;
                    v___y_3503_ = v___x_3500_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_mkMonitorContext___boxed(
    mut v_cfg_3511_: *mut crate::leanh::LeanObject,
    mut v_jobs_3512_: *mut crate::leanh::LeanObject,
    mut v_a_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3514_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_3511_, v_jobs_3512_);
    crate::leanh::lean_dec_ref(v_cfg_3511_);
    return v_res_3514_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(
    mut v_ctx_3515_: *mut crate::leanh::LeanObject,
    mut v_initJobs_3516_: *mut crate::leanh::LeanObject,
    mut v_initFailures_3517_: *mut crate::leanh::LeanObject,
    mut v_resetCtrl_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalJobs_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_3527_: u8 = 0;
    let mut v_failures_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3520_ = lean_io_mono_ms_now();
    v___x_3521_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3522_ = 0;
    v___x_3523_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3523_, 0, v___x_3521_);
    crate::leanh::lean_ctor_set(v___x_3523_, 1, v___x_3521_);
    crate::leanh::lean_ctor_set(v___x_3523_, 2, v_initFailures_3517_);
    crate::leanh::lean_ctor_set(v___x_3523_, 3, v_resetCtrl_3518_);
    crate::leanh::lean_ctor_set(v___x_3523_, 4, v___x_3520_);
    crate::leanh::lean_ctor_set(v___x_3523_, 5, v___x_3521_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3523_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
        v___x_3522_,
    );
    v___x_3524_ =
        l___private_Lake_Build_Run_0__Lake_Monitor_main(v_initJobs_3516_, v_ctx_3515_, v___x_3523_);
    v_snd_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 1);
    crate::leanh::lean_inc(v_snd_3525_);
    crate::leanh::lean_dec_ref(v___x_3524_);
    v_totalJobs_3526_ = crate::leanh::lean_ctor_get(v_snd_3525_, 1);
    crate::leanh::lean_inc(v_totalJobs_3526_);
    v_wantsRebuild_3527_ = crate::leanh::lean_ctor_get_uint8(
        v_snd_3525_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
    );
    v_failures_3528_ = crate::leanh::lean_ctor_get(v_snd_3525_, 2);
    crate::leanh::lean_inc_ref(v_failures_3528_);
    crate::leanh::lean_dec(v_snd_3525_);
    v___x_3529_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3529_, 0, v_failures_3528_);
    crate::leanh::lean_ctor_set(v___x_3529_, 1, v_totalJobs_3526_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3529_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_wantsRebuild_3527_,
    );
    return v___x_3529_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorJobs_x27___boxed(
    mut v_ctx_3530_: *mut crate::leanh::LeanObject,
    mut v_initJobs_3531_: *mut crate::leanh::LeanObject,
    mut v_initFailures_3532_: *mut crate::leanh::LeanObject,
    mut v_resetCtrl_3533_: *mut crate::leanh::LeanObject,
    mut v_a_3534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3535_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(
        v_ctx_3530_,
        v_initJobs_3531_,
        v_initFailures_3532_,
        v_resetCtrl_3533_,
    );
    crate::leanh::lean_dec_ref(v_ctx_3530_);
    return v_res_3535_;
}
pub unsafe fn l_Lake_monitorJobs(
    mut v_initJobs_3536_: *mut crate::leanh::LeanObject,
    mut v_jobs_3537_: *mut crate::leanh::LeanObject,
    mut v_out_3538_: *mut crate::leanh::LeanObject,
    mut v_failLv_3539_: u8,
    mut v_outLv_3540_: u8,
    mut v_minAction_3541_: u8,
    mut v_showOptional_3542_: u8,
    mut v_useAnsi_3543_: u8,
    mut v_showProgress_3544_: u8,
    mut v_showTime_3545_: u8,
    mut v_resetCtrl_3546_: *mut crate::leanh::LeanObject,
    mut v_initFailures_3547_: *mut crate::leanh::LeanObject,
    mut v_updateFrequency_3548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctx_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ctx_3550_ = crate::leanh::lean_alloc_ctor(0, 3, (7) as u32);
    crate::leanh::lean_ctor_set(v_ctx_3550_, 0, v_jobs_3537_);
    crate::leanh::lean_ctor_set(v_ctx_3550_, 1, v_out_3538_);
    crate::leanh::lean_ctor_set(v_ctx_3550_, 2, v_updateFrequency_3548_);
    crate::leanh::lean_ctor_set_uint8(
        v_ctx_3550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_outLv_3540_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ctx_3550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v_failLv_3539_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ctx_3550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
        v_minAction_3541_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ctx_3550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
        v_showOptional_3542_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ctx_3550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
        v_useAnsi_3543_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ctx_3550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
        v_showProgress_3544_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ctx_3550_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
        v_showTime_3545_,
    );
    v___x_3551_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(
        v_ctx_3550_,
        v_initJobs_3536_,
        v_initFailures_3547_,
        v_resetCtrl_3546_,
    );
    crate::leanh::lean_dec_ref_known(v_ctx_3550_, 3);
    return v___x_3551_;
}
pub unsafe fn l_Lake_monitorJobs___boxed(
    mut v_initJobs_3552_: *mut crate::leanh::LeanObject,
    mut v_jobs_3553_: *mut crate::leanh::LeanObject,
    mut v_out_3554_: *mut crate::leanh::LeanObject,
    mut v_failLv_3555_: *mut crate::leanh::LeanObject,
    mut v_outLv_3556_: *mut crate::leanh::LeanObject,
    mut v_minAction_3557_: *mut crate::leanh::LeanObject,
    mut v_showOptional_3558_: *mut crate::leanh::LeanObject,
    mut v_useAnsi_3559_: *mut crate::leanh::LeanObject,
    mut v_showProgress_3560_: *mut crate::leanh::LeanObject,
    mut v_showTime_3561_: *mut crate::leanh::LeanObject,
    mut v_resetCtrl_3562_: *mut crate::leanh::LeanObject,
    mut v_initFailures_3563_: *mut crate::leanh::LeanObject,
    mut v_updateFrequency_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_failLv_boxed_3566_: u8 = 0;
    let mut v_outLv_boxed_3567_: u8 = 0;
    let mut v_minAction_boxed_3568_: u8 = 0;
    let mut v_showOptional_boxed_3569_: u8 = 0;
    let mut v_useAnsi_boxed_3570_: u8 = 0;
    let mut v_showProgress_boxed_3571_: u8 = 0;
    let mut v_showTime_boxed_3572_: u8 = 0;
    let mut v_res_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_failLv_boxed_3566_ = (crate::leanh::lean_unbox(v_failLv_3555_) as u8);
    v_outLv_boxed_3567_ = (crate::leanh::lean_unbox(v_outLv_3556_) as u8);
    v_minAction_boxed_3568_ = (crate::leanh::lean_unbox(v_minAction_3557_) as u8);
    v_showOptional_boxed_3569_ = (crate::leanh::lean_unbox(v_showOptional_3558_) as u8);
    v_useAnsi_boxed_3570_ = (crate::leanh::lean_unbox(v_useAnsi_3559_) as u8);
    v_showProgress_boxed_3571_ = (crate::leanh::lean_unbox(v_showProgress_3560_) as u8);
    v_showTime_boxed_3572_ = (crate::leanh::lean_unbox(v_showTime_3561_) as u8);
    v_res_3573_ = l_Lake_monitorJobs(
        v_initJobs_3552_,
        v_jobs_3553_,
        v_out_3554_,
        v_failLv_boxed_3566_,
        v_outLv_boxed_3567_,
        v_minAction_boxed_3568_,
        v_showOptional_boxed_3569_,
        v_useAnsi_boxed_3570_,
        v_showProgress_boxed_3571_,
        v_showTime_boxed_3572_,
        v_resetCtrl_3562_,
        v_initFailures_3563_,
        v_updateFrequency_3564_,
    );
    return v_res_3573_;
}
pub unsafe fn _init_l_Lake_noBuildCode() -> u32 {
    let mut v___x_3574_: u32 = 0;
    v___x_3574_ = 3;
    return v___x_3574_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(
    mut v_logger_3575_: *mut crate::leanh::LeanObject,
    mut v_x_3576_: *mut crate::leanh::LeanObject,
    mut v___y_3577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3579_ =
        crate::leanh::lean_apply_2(v_logger_3575_, v___y_3577_, crate::leanh::lean_box(0));
    return v___x_3579_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed(
    mut v_logger_3580_: *mut crate::leanh::LeanObject,
    mut v_x_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
    mut v___y_3583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3584_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0(
        v_logger_3580_,
        v_x_3581_,
        v___y_3582_,
    );
    return v_res_3584_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3585_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqBool___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_3586_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3586_, 0, v___x_3585_);
    return v___f_3586_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3593_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3;
    v___x_3594_ = l_String_quote(v___x_3593_);
    return v___x_3594_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3595_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4_once
        ),
        _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__4,
    );
    v___x_3596_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3596_, 0, v___x_3595_);
    return v___x_3596_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3597_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3598_ = l_Std_Format_defWidth;
    v___x_3599_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5_once
        ),
        _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__5,
    );
    v___x_3600_ = l_Std_Format_pretty(v___x_3599_, v___x_3598_, v___x_3597_, v___x_3597_);
    return v___x_3600_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3602_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7;
    v___x_3603_ = l_String_quote(v___x_3602_);
    return v___x_3603_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3604_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8_once
        ),
        _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__8,
    );
    v___x_3605_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3605_, 0, v___x_3604_);
    return v___x_3605_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3606_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3607_ = l_Std_Format_defWidth;
    v___x_3608_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9_once
        ),
        _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__9,
    );
    v___x_3609_ = l_Std_Format_pretty(v___x_3608_, v___x_3607_, v___x_3606_, v___x_3606_);
    return v___x_3609_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3611_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11;
    v___x_3612_ = l_String_quote(v___x_3611_);
    return v___x_3612_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3613_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12_once
        ),
        _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__12,
    );
    v___x_3614_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3614_, 0, v___x_3613_);
    return v___x_3614_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3615_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3616_ = l_Std_Format_defWidth;
    v___x_3617_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13_once
        ),
        _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__13,
    );
    v___x_3618_ = l_Std_Format_pretty(v___x_3617_, v___x_3616_, v___x_3615_, v___x_3615_);
    return v___x_3618_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(
    mut v_logger_3620_: *mut crate::leanh::LeanObject,
    mut v_ws_3621_: *mut crate::leanh::LeanObject,
    mut v_outputsRef_x3f_3622_: *mut crate::leanh::LeanObject,
    mut v_out_3623_: *mut crate::leanh::LeanObject,
    mut v_outputsFile_3624_: *mut crate::leanh::LeanObject,
    mut v_isVerbose_3625_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3637_: u8 = 0;
    let mut v___x_3638_: usize = 0;
    let mut v___x_3639_: usize = 0;
    let mut v___x_1971__overap_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: usize = 0;
    let mut v___x_3643_: usize = 0;
    let mut v___x_1975__overap_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: u8 = 0;
    let mut v___x_3654_: usize = 0;
    let mut v___x_3655_: usize = 0;
    let mut v___x_1875__overap_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: usize = 0;
    let mut v___x_3659_: usize = 0;
    let mut v___x_1879__overap_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: u8 = 0;
    let mut v_putStr_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113__overap_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770__overap_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925__overap_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: u8 = 0;
    let mut v_packages_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: u8 = 0;
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_logger_3620_);
                v___f_3629_ = crate::leanh::lean_alloc_closure(
                    l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3629_, 0, v_logger_3620_);
                v___x_3630_ = l_instMonadBaseIO;
                v___x_3743_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_3621_);
                if v___x_3743_ == 0 {
                    v_packages_3744_ = crate::leanh::lean_ctor_get(v_ws_3621_, 4);
                    v___x_3745_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3746_ = lean_array_fget_borrowed(v_packages_3744_, v___x_3745_);
                    v_baseName_3747_ = crate::leanh::lean_ctor_get(v___x_3746_, 1);
                    crate::leanh::lean_inc(v_baseName_3747_);
                    v___x_3748_ = l_Lean_Name_toString(v_baseName_3747_, v___x_3743_);
                    v___x_3749_ =
                        l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15;
                    v___x_3750_ = lean_string_append(v___x_3748_, v___x_3749_);
                    v___x_3751_ = 2;
                    v___x_3752_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3752_, 0, v___x_3750_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3752_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3751_,
                    );
                    v___x_3753_ = crate::leanh::lean_apply_2(
                        v_logger_3620_,
                        v___x_3752_,
                        crate::leanh::lean_box(0),
                    );
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_logger_3620_);
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_3628_ = crate::leanh::lean_box(0);
                return v___x_3628_;
            }
            2 => {
                v___x_3634_ = lean_array_get_size(v___y_3632_);
                v___x_3635_ = crate::leanh::lean_box(0);
                v___x_3636_ = lean_nat_dec_lt(v___y_3633_, v___x_3634_);
                if v___x_3636_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3632_);
                    crate::leanh::lean_dec_ref(v___f_3629_);
                    return v___x_3635_;
                } else {
                    v___x_3637_ = lean_nat_dec_le(v___x_3634_, v___x_3634_);
                    if v___x_3637_ == 0 {
                        if v___x_3636_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_3632_);
                            crate::leanh::lean_dec_ref(v___f_3629_);
                            return v___x_3635_;
                        } else {
                            v___x_3638_ = 0usize;
                            v___x_3639_ = lean_usize_of_nat(v___x_3634_);
                            v___x_1971__overap_3640_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_3630_,
                                    v___f_3629_,
                                    v___y_3632_,
                                    v___x_3638_,
                                    v___x_3639_,
                                    v___x_3635_,
                                );
                            v___x_3641_ = crate::leanh::lean_apply_1(
                                v___x_1971__overap_3640_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_3641_;
                        }
                    } else {
                        v___x_3642_ = 0usize;
                        v___x_3643_ = lean_usize_of_nat(v___x_3634_);
                        v___x_1975__overap_3644_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_3630_,
                                v___f_3629_,
                                v___y_3632_,
                                v___x_3642_,
                                v___x_3643_,
                                v___x_3635_,
                            );
                        v___x_3645_ = crate::leanh::lean_apply_1(
                            v___x_1975__overap_3644_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3645_;
                    }
                }
            }
            3 => {
                if v_isVerbose_3625_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3647_);
                    crate::leanh::lean_dec_ref(v___f_3629_);
                    v___x_3649_ = crate::leanh::lean_box(0);
                    return v___x_3649_;
                } else {
                    v___x_3650_ = lean_array_get_size(v___y_3647_);
                    v___x_3651_ = crate::leanh::lean_box(0);
                    v___x_3652_ = lean_nat_dec_lt(v___y_3648_, v___x_3650_);
                    if v___x_3652_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_3647_);
                        crate::leanh::lean_dec_ref(v___f_3629_);
                        return v___x_3651_;
                    } else {
                        v___x_3653_ = lean_nat_dec_le(v___x_3650_, v___x_3650_);
                        if v___x_3653_ == 0 {
                            if v___x_3652_ == 0 {
                                crate::leanh::lean_dec_ref(v___y_3647_);
                                crate::leanh::lean_dec_ref(v___f_3629_);
                                return v___x_3651_;
                            } else {
                                v___x_3654_ = 0usize;
                                v___x_3655_ = lean_usize_of_nat(v___x_3650_);
                                v___x_1875__overap_3656_ =
                                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_3630_,
                                        v___f_3629_,
                                        v___y_3647_,
                                        v___x_3654_,
                                        v___x_3655_,
                                        v___x_3651_,
                                    );
                                v___x_3657_ = crate::leanh::lean_apply_1(
                                    v___x_1875__overap_3656_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_3657_;
                            }
                        } else {
                            v___x_3658_ = 0usize;
                            v___x_3659_ = lean_usize_of_nat(v___x_3650_);
                            v___x_1879__overap_3660_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_3630_,
                                    v___f_3629_,
                                    v___y_3647_,
                                    v___x_3658_,
                                    v___x_3659_,
                                    v___x_3651_,
                                );
                            v___x_3661_ = crate::leanh::lean_apply_1(
                                v___x_1879__overap_3660_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_3661_;
                        }
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_outputsRef_x3f_3622_) == 1 {
                    v_val_3663_ = crate::leanh::lean_ctor_get(v_outputsRef_x3f_3622_, 0);
                    v___x_3664_ = lean_st_ref_get(v_val_3663_);
                    v_packages_3665_ = crate::leanh::lean_ctor_get(v_ws_3621_, 4);
                    v___x_3666_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3667_ = lean_array_fget_borrowed(v_packages_3665_, v___x_3666_);
                    v_config_3668_ = crate::leanh::lean_ctor_get(v___x_3667_, 6);
                    v_toLeanConfig_3669_ = crate::leanh::lean_ctor_get(v_config_3668_, 1);
                    v_platformIndependent_3670_ =
                        crate::leanh::lean_ctor_get(v_toLeanConfig_3669_, 10);
                    v___f_3671_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0_once), _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__0);
                    v___x_3672_ =
                        l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1;
                    crate::leanh::lean_inc(v_platformIndependent_3670_);
                    v___x_3673_ = l_Option_instBEq_beq___redArg(
                        v___f_3671_,
                        v_platformIndependent_3670_,
                        v___x_3672_,
                    );
                    v___x_3674_ =
                        l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2;
                    v___x_3675_ = l_Lake_CacheMap_writeFile(
                        v_outputsFile_3624_,
                        v___x_3664_,
                        v___x_3673_,
                        v___x_3674_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3675_) == 0 {
                        v_a_3676_ = crate::leanh::lean_ctor_get(v___x_3675_, 1);
                        crate::leanh::lean_inc(v_a_3676_);
                        crate::leanh::lean_dec_ref_known(v___x_3675_, 2);
                        v___x_3677_ = lean_array_get_size(v_a_3676_);
                        v___x_3678_ = lean_nat_dec_eq(v___x_3677_, v___x_3666_);
                        if v___x_3678_ == 0 {
                            if v_isVerbose_3625_ == 0 {
                                crate::leanh::lean_dec(v_a_3676_);
                                crate::leanh::lean_dec_ref(v___f_3629_);
                                crate::leanh::lean_dec_ref(v_out_3623_);
                                state = 1;
                                continue;
                            } else {
                                v_putStr_3679_ = crate::leanh::lean_ctor_get(v_out_3623_, 4);
                                crate::leanh::lean_inc_ref(v_putStr_3679_);
                                crate::leanh::lean_dec_ref(v_out_3623_);
                                v___x_3680_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3;
                                v___x_3681_ = crate::leanh::lean_apply_2(
                                    v_putStr_3679_,
                                    v___x_3680_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_3681_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3681_, 1);
                                    v___y_3632_ = v_a_3676_;
                                    v___y_3633_ = v___x_3666_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_3682_ = crate::leanh::lean_ctor_get(v___x_3681_, 0);
                                    crate::leanh::lean_inc(v_a_3682_);
                                    crate::leanh::lean_dec_ref_known(v___x_3681_, 1);
                                    v___x_3683_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__0), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once), _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0);
                                    v___x_3684_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                                    v___x_3685_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                                    v___x_3686_ = crate::leanh::lean_unsigned_to_nat(89);
                                    v___x_3687_ = crate::leanh::lean_unsigned_to_nat(4);
                                    v___x_3688_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
                                    v___x_3689_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
                                    v___x_3690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3689_, v_isVerbose_3625_);
                                    v___x_3691_ = lean_string_append(v___x_3688_, v___x_3690_);
                                    crate::leanh::lean_dec_ref(v___x_3690_);
                                    v___x_3692_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
                                    v___x_3693_ = lean_string_append(v___x_3691_, v___x_3692_);
                                    v___x_3694_ = lean_io_error_to_string(v_a_3682_);
                                    v___x_3695_ = lean_string_append(v___x_3693_, v___x_3694_);
                                    crate::leanh::lean_dec_ref(v___x_3694_);
                                    v___x_3696_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                                    v___x_3697_ = lean_string_append(v___x_3695_, v___x_3696_);
                                    v___x_3698_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once), _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
                                    v___x_3699_ = lean_string_append(v___x_3697_, v___x_3698_);
                                    v___x_3700_ = l_mkPanicMessageWithDecl(
                                        v___x_3684_,
                                        v___x_3685_,
                                        v___x_3686_,
                                        v___x_3687_,
                                        v___x_3699_,
                                    );
                                    crate::leanh::lean_dec_ref(v___x_3699_);
                                    v___x_2113__overap_3701_ =
                                        l_panic___redArg(v___x_3683_, v___x_3700_);
                                    v___x_3702_ = crate::leanh::lean_apply_1(
                                        v___x_2113__overap_3701_,
                                        crate::leanh::lean_box(0),
                                    );
                                    v___y_3632_ = v_a_3676_;
                                    v___y_3633_ = v___x_3666_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3676_);
                            crate::leanh::lean_dec_ref(v___f_3629_);
                            crate::leanh::lean_dec_ref(v_out_3623_);
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3703_ = crate::leanh::lean_ctor_get(v___x_3675_, 1);
                        crate::leanh::lean_inc(v_a_3703_);
                        crate::leanh::lean_dec_ref_known(v___x_3675_, 2);
                        v_putStr_3704_ = crate::leanh::lean_ctor_get(v_out_3623_, 4);
                        crate::leanh::lean_inc_ref(v_putStr_3704_);
                        crate::leanh::lean_dec_ref(v_out_3623_);
                        v___x_3705_ =
                            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7;
                        v___x_3706_ = crate::leanh::lean_apply_2(
                            v_putStr_3704_,
                            v___x_3705_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_3706_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3706_, 1);
                            v___y_3647_ = v_a_3703_;
                            v___y_3648_ = v___x_3666_;
                            state = 3;
                            continue;
                        } else {
                            v_a_3707_ = crate::leanh::lean_ctor_get(v___x_3706_, 0);
                            crate::leanh::lean_inc(v_a_3707_);
                            crate::leanh::lean_dec_ref_known(v___x_3706_, 1);
                            v___x_3708_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_Build_Run_0__Lake_print_x21___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once
                                ),
                                _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0,
                            );
                            v___x_3709_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                            v___x_3710_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                            v___x_3711_ = crate::leanh::lean_unsigned_to_nat(89);
                            v___x_3712_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_3713_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_Build_Run_0__Lake_print_x21___closed__19
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once
                                ),
                                _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19,
                            );
                            v___x_3714_ = lean_io_error_to_string(v_a_3707_);
                            v___x_3715_ = lean_string_append(v___x_3713_, v___x_3714_);
                            crate::leanh::lean_dec_ref(v___x_3714_);
                            v___x_3716_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                            v___x_3717_ = lean_string_append(v___x_3715_, v___x_3716_);
                            v___x_3718_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once), _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
                            v___x_3719_ = lean_string_append(v___x_3717_, v___x_3718_);
                            v___x_3720_ = l_mkPanicMessageWithDecl(
                                v___x_3709_,
                                v___x_3710_,
                                v___x_3711_,
                                v___x_3712_,
                                v___x_3719_,
                            );
                            crate::leanh::lean_dec_ref(v___x_3719_);
                            v___x_1770__overap_3721_ = l_panic___redArg(v___x_3708_, v___x_3720_);
                            v___x_3722_ = crate::leanh::lean_apply_1(
                                v___x_1770__overap_3721_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_3647_ = v_a_3703_;
                            v___y_3648_ = v___x_3666_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_3629_);
                    crate::leanh::lean_dec_ref(v_outputsFile_3624_);
                    v_putStr_3723_ = crate::leanh::lean_ctor_get(v_out_3623_, 4);
                    crate::leanh::lean_inc_ref(v_putStr_3723_);
                    crate::leanh::lean_dec_ref(v_out_3623_);
                    v___x_3724_ =
                        l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11;
                    v___x_3725_ = crate::leanh::lean_apply_2(
                        v_putStr_3723_,
                        v___x_3724_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3725_) == 0 {
                        v_a_3726_ = crate::leanh::lean_ctor_get(v___x_3725_, 0);
                        crate::leanh::lean_inc(v_a_3726_);
                        crate::leanh::lean_dec_ref_known(v___x_3725_, 1);
                        return v_a_3726_;
                    } else {
                        v_a_3727_ = crate::leanh::lean_ctor_get(v___x_3725_, 0);
                        crate::leanh::lean_inc(v_a_3727_);
                        crate::leanh::lean_dec_ref_known(v___x_3725_, 1);
                        v___x_3728_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_print_x21___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_print_x21___closed__0_once
                            ),
                            _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__0,
                        );
                        v___x_3729_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                        v___x_3730_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                        v___x_3731_ = crate::leanh::lean_unsigned_to_nat(89);
                        v___x_3732_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_3733_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_print_x21___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once
                            ),
                            _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19,
                        );
                        v___x_3734_ = lean_io_error_to_string(v_a_3727_);
                        v___x_3735_ = lean_string_append(v___x_3733_, v___x_3734_);
                        crate::leanh::lean_dec_ref(v___x_3734_);
                        v___x_3736_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                        v___x_3737_ = lean_string_append(v___x_3735_, v___x_3736_);
                        v___x_3738_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once), _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14);
                        v___x_3739_ = lean_string_append(v___x_3737_, v___x_3738_);
                        v___x_3740_ = l_mkPanicMessageWithDecl(
                            v___x_3729_,
                            v___x_3730_,
                            v___x_3731_,
                            v___x_3732_,
                            v___x_3739_,
                        );
                        crate::leanh::lean_dec_ref(v___x_3739_);
                        v___x_1925__overap_3741_ = l_panic___redArg(v___x_3728_, v___x_3740_);
                        v___x_3742_ = crate::leanh::lean_apply_1(
                            v___x_1925__overap_3741_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3742_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___boxed(
    mut v_logger_3754_: *mut crate::leanh::LeanObject,
    mut v_ws_3755_: *mut crate::leanh::LeanObject,
    mut v_outputsRef_x3f_3756_: *mut crate::leanh::LeanObject,
    mut v_out_3757_: *mut crate::leanh::LeanObject,
    mut v_outputsFile_3758_: *mut crate::leanh::LeanObject,
    mut v_isVerbose_3759_: *mut crate::leanh::LeanObject,
    mut v_a_3760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isVerbose_boxed_3761_: u8 = 0;
    let mut v_res_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isVerbose_boxed_3761_ = (crate::leanh::lean_unbox(v_isVerbose_3759_) as u8);
    v_res_3762_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs(
        v_logger_3754_,
        v_ws_3755_,
        v_outputsRef_x3f_3756_,
        v_out_3757_,
        v_outputsFile_3758_,
        v_isVerbose_boxed_3761_,
    );
    crate::leanh::lean_dec(v_outputsRef_x3f_3756_);
    crate::leanh::lean_dec_ref(v_ws_3755_);
    return v_res_3762_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(
    mut v_out_3764_: *mut crate::leanh::LeanObject,
    mut v_as_3765_: *mut crate::leanh::LeanObject,
    mut v_i_3766_: usize,
    mut v_stop_3767_: usize,
    mut v_b_3768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: usize = 0;
    let mut v___x_3773_: usize = 0;
    let mut v___x_3775_: u8 = 0;
    let mut v_putStr_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3787_: u8 = 0;
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3775_ = lean_usize_dec_eq(v_i_3766_, v_stop_3767_);
                if v___x_3775_ == 0 {
                    v_putStr_3776_ = crate::leanh::lean_ctor_get(v_out_3764_, 4);
                    v___x_3777_ = lean_array_uget_borrowed(v_as_3765_, v_i_3766_);
                    v___x_3778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___closed__0;
                    v___x_3779_ = lean_string_append(v___x_3778_, v___x_3777_);
                    v___x_3780_ = l___private_Lake_Build_Run_0__Lake_Monitor_reportJob___closed__0;
                    v___x_3781_ = lean_string_append(v___x_3779_, v___x_3780_);
                    crate::leanh::lean_inc_ref(v_putStr_3776_);
                    crate::leanh::lean_inc_ref(v___x_3781_);
                    v___x_3782_ = crate::leanh::lean_apply_2(
                        v_putStr_3776_,
                        v___x_3781_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3782_) == 0 {
                        crate::leanh::lean_dec_ref(v___x_3781_);
                        v_a_3783_ = crate::leanh::lean_ctor_get(v___x_3782_, 0);
                        crate::leanh::lean_inc(v_a_3783_);
                        crate::leanh::lean_dec_ref_known(v___x_3782_, 1);
                        v_val_3771_ = v_a_3783_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3784_ = crate::leanh::lean_ctor_get(v___x_3782_, 0);
                        v_isSharedCheck_3807_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3782_)) as u8;
                        if v_isSharedCheck_3807_ == 0 {
                            v___x_3786_ = v___x_3782_;
                            v_isShared_3787_ = v_isSharedCheck_3807_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3784_);
                            crate::leanh::lean_dec(v___x_3782_);
                            v___x_3786_ = crate::leanh::lean_box(0);
                            v_isShared_3787_ = v_isSharedCheck_3807_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_out_3764_);
                    return v_b_3768_;
                }
            }
            1 => {
                v___x_3772_ = 1usize;
                v___x_3773_ = lean_usize_add(v_i_3766_, v___x_3772_);
                v_i_3766_ = v___x_3773_;
                v_b_3768_ = v_val_3771_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3788_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                v___x_3789_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                v___x_3790_ = crate::leanh::lean_unsigned_to_nat(89);
                v___x_3791_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3792_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3793_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once
                    ),
                    _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19,
                );
                v___x_3794_ = lean_io_error_to_string(v_a_3784_);
                v___x_3795_ = lean_string_append(v___x_3793_, v___x_3794_);
                crate::leanh::lean_dec_ref(v___x_3794_);
                v___x_3796_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                v___x_3797_ = lean_string_append(v___x_3795_, v___x_3796_);
                v___x_3798_ = l_String_quote(v___x_3781_);
                if v_isShared_3787_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3786_, 3);
                    crate::leanh::lean_ctor_set(v___x_3786_, 0, v___x_3798_);
                    v___x_3800_ = v___x_3786_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3806_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3798_);
                    v___x_3800_ = v_reuseFailAlloc_3806_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3801_ = l_Std_Format_defWidth;
                v___x_3802_ =
                    l_Std_Format_pretty(v___x_3800_, v___x_3801_, v___x_3792_, v___x_3792_);
                v___x_3803_ = lean_string_append(v___x_3797_, v___x_3802_);
                crate::leanh::lean_dec_ref(v___x_3802_);
                v___x_3804_ = l_mkPanicMessageWithDecl(
                    v___x_3788_,
                    v___x_3789_,
                    v___x_3790_,
                    v___x_3791_,
                    v___x_3803_,
                );
                crate::leanh::lean_dec_ref(v___x_3803_);
                v___x_3805_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_3804_);
                v_val_3771_ = v___x_3805_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0___boxed(
    mut v_out_3808_: *mut crate::leanh::LeanObject,
    mut v_as_3809_: *mut crate::leanh::LeanObject,
    mut v_i_3810_: *mut crate::leanh::LeanObject,
    mut v_stop_3811_: *mut crate::leanh::LeanObject,
    mut v_b_3812_: *mut crate::leanh::LeanObject,
    mut v___y_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3814_: usize = 0;
    let mut v_stop_boxed_3815_: usize = 0;
    let mut v_res_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3814_ = crate::leanh::lean_unbox_usize(v_i_3810_);
    crate::leanh::lean_dec(v_i_3810_);
    v_stop_boxed_3815_ = crate::leanh::lean_unbox_usize(v_stop_3811_);
    crate::leanh::lean_dec(v_stop_3811_);
    v_res_3816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_3808_, v_as_3809_, v_i_boxed_3814_, v_stop_boxed_3815_, v_b_3812_);
    crate::leanh::lean_dec_ref(v_as_3809_);
    return v_res_3816_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = l___private_Lake_Build_Run_0__Lake_reportResult___closed__5;
    v___x_3824_ = l_String_quote(v___x_3823_);
    return v___x_3824_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__6),
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__6_once),
        _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__6,
    );
    v___x_3826_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3826_, 0, v___x_3825_);
    return v___x_3826_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3828_ = l_Std_Format_defWidth;
    v___x_3829_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__7),
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__7_once),
        _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__7,
    );
    v___x_3830_ = l_Std_Format_pretty(v___x_3829_, v___x_3828_, v___x_3827_, v___x_3827_);
    return v___x_3830_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3832_ = l___private_Lake_Build_Run_0__Lake_reportResult___closed__9;
    v___x_3833_ = l_String_quote(v___x_3832_);
    return v___x_3833_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3834_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__10),
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__10_once),
        _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__10,
    );
    v___x_3835_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3835_, 0, v___x_3834_);
    return v___x_3835_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3836_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3837_ = l_Std_Format_defWidth;
    v___x_3838_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__11),
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__11_once),
        _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__11,
    );
    v___x_3839_ = l_Std_Format_pretty(v___x_3838_, v___x_3837_, v___x_3836_, v___x_3836_);
    return v___x_3839_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_reportResult(
    mut v_cfg_3840_: *mut crate::leanh::LeanObject,
    mut v_out_3841_: *mut crate::leanh::LeanObject,
    mut v_result_3842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3845_: u8 = 0;
    let mut v___y_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noBuild_3847_: u8 = 0;
    let mut v_putStr_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3858_: u8 = 0;
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut v_putStr_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut v_failures_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numJobs_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: u8 = 0;
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: u8 = 0;
    let mut v_flush_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: u8 = 0;
    let mut v___x_3971_: usize = 0;
    let mut v___x_3972_: usize = 0;
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: usize = 0;
    let mut v___x_3975_: usize = 0;
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: u8 = 0;
    let mut v_showSuccess_3994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_failures_3920_ = crate::leanh::lean_ctor_get(v_result_3842_, 0);
                crate::leanh::lean_inc_ref(v_failures_3920_);
                v_numJobs_3921_ = crate::leanh::lean_ctor_get(v_result_3842_, 1);
                crate::leanh::lean_inc(v_numJobs_3921_);
                crate::leanh::lean_dec_ref(v_result_3842_);
                v___x_3956_ = lean_array_get_size(v_failures_3920_);
                v___x_3957_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3958_ = lean_nat_dec_eq(v___x_3956_, v___x_3957_);
                if v___x_3958_ == 0 {
                    crate::leanh::lean_dec(v_numJobs_3921_);
                    v_flush_3959_ = crate::leanh::lean_ctor_get(v_out_3841_, 0);
                    crate::leanh::lean_inc_ref(v_flush_3959_);
                    v_putStr_3960_ = crate::leanh::lean_ctor_get(v_out_3841_, 4);
                    v___x_3977_ = l___private_Lake_Build_Run_0__Lake_reportResult___closed__9;
                    crate::leanh::lean_inc_ref(v_putStr_3960_);
                    v___x_3978_ = crate::leanh::lean_apply_2(
                        v_putStr_3960_,
                        v___x_3977_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3978_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3978_, 1);
                        state = 9;
                        continue;
                    } else {
                        v_a_3979_ = crate::leanh::lean_ctor_get(v___x_3978_, 0);
                        crate::leanh::lean_inc(v_a_3979_);
                        crate::leanh::lean_dec_ref_known(v___x_3978_, 1);
                        v___x_3980_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                        v___x_3981_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                        v___x_3982_ = crate::leanh::lean_unsigned_to_nat(89);
                        v___x_3983_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_3984_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_print_x21___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once
                            ),
                            _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19,
                        );
                        v___x_3985_ = lean_io_error_to_string(v_a_3979_);
                        v___x_3986_ = lean_string_append(v___x_3984_, v___x_3985_);
                        crate::leanh::lean_dec_ref(v___x_3985_);
                        v___x_3987_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                        v___x_3988_ = lean_string_append(v___x_3986_, v___x_3987_);
                        v___x_3989_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_reportResult___closed__12
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_reportResult___closed__12_once
                            ),
                            _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__12,
                        );
                        v___x_3990_ = lean_string_append(v___x_3988_, v___x_3989_);
                        v___x_3991_ = l_mkPanicMessageWithDecl(
                            v___x_3980_,
                            v___x_3981_,
                            v___x_3982_,
                            v___x_3983_,
                            v___x_3990_,
                        );
                        crate::leanh::lean_dec_ref(v___x_3990_);
                        v___x_3992_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_3991_);
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_failures_3920_);
                    v___x_3993_ = l_Lake_BuildConfig_showProgress(v_cfg_3840_);
                    if v___x_3993_ == 0 {
                        v___y_3923_ = v___x_3993_;
                        state = 6;
                        continue;
                    } else {
                        v_showSuccess_3994_ = crate::leanh::lean_ctor_get_uint8(
                            v_cfg_3840_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                        );
                        v___y_3923_ = v_showSuccess_3994_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_noBuild_3847_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_3840_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                );
                if v_noBuild_3847_ == 0 {
                    v_putStr_3848_ = crate::leanh::lean_ctor_get(v_out_3841_, 4);
                    crate::leanh::lean_inc_ref(v_putStr_3848_);
                    crate::leanh::lean_dec_ref(v_out_3841_);
                    v___x_3849_ = l___private_Lake_Build_Run_0__Lake_reportResult___closed__0;
                    v___x_3850_ = lean_string_append(v___x_3849_, v___y_3846_);
                    crate::leanh::lean_dec_ref(v___y_3846_);
                    v___x_3851_ = l___private_Lake_Build_Run_0__Lake_reportResult___closed__1;
                    v___x_3852_ = lean_string_append(v___x_3850_, v___x_3851_);
                    crate::leanh::lean_inc_ref(v___x_3852_);
                    v___x_3853_ = crate::leanh::lean_apply_2(
                        v_putStr_3848_,
                        v___x_3852_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3853_) == 0 {
                        crate::leanh::lean_dec_ref(v___x_3852_);
                        v_a_3854_ = crate::leanh::lean_ctor_get(v___x_3853_, 0);
                        crate::leanh::lean_inc(v_a_3854_);
                        crate::leanh::lean_dec_ref_known(v___x_3853_, 1);
                        return v_a_3854_;
                    } else {
                        v_a_3855_ = crate::leanh::lean_ctor_get(v___x_3853_, 0);
                        v_isSharedCheck_3883_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3853_)) as u8;
                        if v_isSharedCheck_3883_ == 0 {
                            v___x_3857_ = v___x_3853_;
                            v_isShared_3858_ = v_isSharedCheck_3883_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3855_);
                            crate::leanh::lean_dec(v___x_3853_);
                            v___x_3857_ = crate::leanh::lean_box(0);
                            v_isShared_3858_ = v_isSharedCheck_3883_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_putStr_3884_ = crate::leanh::lean_ctor_get(v_out_3841_, 4);
                    crate::leanh::lean_inc_ref(v_putStr_3884_);
                    crate::leanh::lean_dec_ref(v_out_3841_);
                    v___x_3885_ = l___private_Lake_Build_Run_0__Lake_reportResult___closed__2;
                    v___x_3886_ = lean_string_append(v___x_3885_, v___y_3846_);
                    crate::leanh::lean_dec_ref(v___y_3846_);
                    v___x_3887_ = l___private_Lake_Build_Run_0__Lake_reportResult___closed__1;
                    v___x_3888_ = lean_string_append(v___x_3886_, v___x_3887_);
                    crate::leanh::lean_inc_ref(v___x_3888_);
                    v___x_3889_ = crate::leanh::lean_apply_2(
                        v_putStr_3884_,
                        v___x_3888_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3889_) == 0 {
                        crate::leanh::lean_dec_ref(v___x_3888_);
                        v_a_3890_ = crate::leanh::lean_ctor_get(v___x_3889_, 0);
                        crate::leanh::lean_inc(v_a_3890_);
                        crate::leanh::lean_dec_ref_known(v___x_3889_, 1);
                        return v_a_3890_;
                    } else {
                        v_a_3891_ = crate::leanh::lean_ctor_get(v___x_3889_, 0);
                        v_isSharedCheck_3919_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3889_)) as u8;
                        if v_isSharedCheck_3919_ == 0 {
                            v___x_3893_ = v___x_3889_;
                            v_isShared_3894_ = v_isSharedCheck_3919_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3891_);
                            crate::leanh::lean_dec(v___x_3889_);
                            v___x_3893_ = crate::leanh::lean_box(0);
                            v_isShared_3894_ = v_isSharedCheck_3919_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3859_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                v___x_3860_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                v___x_3861_ = crate::leanh::lean_unsigned_to_nat(89);
                v___x_3862_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3863_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
                v___x_3864_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3865_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
                v___x_3866_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_3865_,
                    v___y_3845_,
                );
                v___x_3867_ = lean_string_append(v___x_3863_, v___x_3866_);
                crate::leanh::lean_dec_ref(v___x_3866_);
                v___x_3868_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
                v___x_3869_ = lean_string_append(v___x_3867_, v___x_3868_);
                v___x_3870_ = lean_io_error_to_string(v_a_3855_);
                v___x_3871_ = lean_string_append(v___x_3869_, v___x_3870_);
                crate::leanh::lean_dec_ref(v___x_3870_);
                v___x_3872_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                v___x_3873_ = lean_string_append(v___x_3871_, v___x_3872_);
                v___x_3874_ = l_String_quote(v___x_3852_);
                if v_isShared_3858_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3857_, 3);
                    crate::leanh::lean_ctor_set(v___x_3857_, 0, v___x_3874_);
                    v___x_3876_ = v___x_3857_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3874_);
                    v___x_3876_ = v_reuseFailAlloc_3882_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3877_ = l_Std_Format_defWidth;
                v___x_3878_ =
                    l_Std_Format_pretty(v___x_3876_, v___x_3877_, v___x_3864_, v___x_3864_);
                v___x_3879_ = lean_string_append(v___x_3873_, v___x_3878_);
                crate::leanh::lean_dec_ref(v___x_3878_);
                v___x_3880_ = l_mkPanicMessageWithDecl(
                    v___x_3859_,
                    v___x_3860_,
                    v___x_3861_,
                    v___x_3862_,
                    v___x_3879_,
                );
                crate::leanh::lean_dec_ref(v___x_3879_);
                v___x_3881_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_3880_);
                return v___x_3881_;
            }
            4 => {
                v___x_3895_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                v___x_3896_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                v___x_3897_ = crate::leanh::lean_unsigned_to_nat(89);
                v___x_3898_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3899_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
                v___x_3900_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3901_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
                v___x_3902_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_3901_,
                    v_noBuild_3847_,
                );
                v___x_3903_ = lean_string_append(v___x_3899_, v___x_3902_);
                crate::leanh::lean_dec_ref(v___x_3902_);
                v___x_3904_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
                v___x_3905_ = lean_string_append(v___x_3903_, v___x_3904_);
                v___x_3906_ = lean_io_error_to_string(v_a_3891_);
                v___x_3907_ = lean_string_append(v___x_3905_, v___x_3906_);
                crate::leanh::lean_dec_ref(v___x_3906_);
                v___x_3908_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                v___x_3909_ = lean_string_append(v___x_3907_, v___x_3908_);
                v___x_3910_ = l_String_quote(v___x_3888_);
                if v_isShared_3894_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3893_, 3);
                    crate::leanh::lean_ctor_set(v___x_3893_, 0, v___x_3910_);
                    v___x_3912_ = v___x_3893_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3918_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3910_);
                    v___x_3912_ = v_reuseFailAlloc_3918_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3913_ = l_Std_Format_defWidth;
                v___x_3914_ =
                    l_Std_Format_pretty(v___x_3912_, v___x_3913_, v___x_3900_, v___x_3900_);
                v___x_3915_ = lean_string_append(v___x_3909_, v___x_3914_);
                crate::leanh::lean_dec_ref(v___x_3914_);
                v___x_3916_ = l_mkPanicMessageWithDecl(
                    v___x_3895_,
                    v___x_3896_,
                    v___x_3897_,
                    v___x_3898_,
                    v___x_3915_,
                );
                crate::leanh::lean_dec_ref(v___x_3915_);
                v___x_3917_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_3916_);
                return v___x_3917_;
            }
            6 => {
                if v___y_3923_ == 0 {
                    crate::leanh::lean_dec(v_numJobs_3921_);
                    crate::leanh::lean_dec_ref(v_out_3841_);
                    v___x_3924_ = crate::leanh::lean_box(0);
                    return v___x_3924_;
                } else {
                    v___x_3925_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3926_ = lean_nat_dec_eq(v_numJobs_3921_, v___x_3925_);
                    if v___x_3926_ == 0 {
                        v___x_3927_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3928_ = lean_nat_dec_eq(v_numJobs_3921_, v___x_3927_);
                        if v___x_3928_ == 0 {
                            v___x_3929_ = l_Nat_reprFast(v_numJobs_3921_);
                            v___x_3930_ =
                                l___private_Lake_Build_Run_0__Lake_reportResult___closed__3;
                            v___x_3931_ = lean_string_append(v___x_3929_, v___x_3930_);
                            v___y_3845_ = v___y_3923_;
                            v___y_3846_ = v___x_3931_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_numJobs_3921_);
                            v___x_3932_ =
                                l___private_Lake_Build_Run_0__Lake_reportResult___closed__4;
                            v___y_3845_ = v___y_3923_;
                            v___y_3846_ = v___x_3932_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_numJobs_3921_);
                        v_putStr_3933_ = crate::leanh::lean_ctor_get(v_out_3841_, 4);
                        crate::leanh::lean_inc_ref(v_putStr_3933_);
                        crate::leanh::lean_dec_ref(v_out_3841_);
                        v___x_3934_ = l___private_Lake_Build_Run_0__Lake_reportResult___closed__5;
                        v___x_3935_ = crate::leanh::lean_apply_2(
                            v_putStr_3933_,
                            v___x_3934_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_3935_) == 0 {
                            v_a_3936_ = crate::leanh::lean_ctor_get(v___x_3935_, 0);
                            crate::leanh::lean_inc(v_a_3936_);
                            crate::leanh::lean_dec_ref_known(v___x_3935_, 1);
                            return v_a_3936_;
                        } else {
                            v_a_3937_ = crate::leanh::lean_ctor_get(v___x_3935_, 0);
                            crate::leanh::lean_inc(v_a_3937_);
                            crate::leanh::lean_dec_ref_known(v___x_3935_, 1);
                            v___x_3938_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                            v___x_3939_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                            v___x_3940_ = crate::leanh::lean_unsigned_to_nat(89);
                            v___x_3941_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_3942_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
                            v___x_3943_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
                            v___x_3944_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_3943_,
                                    v___x_3926_,
                                );
                            v___x_3945_ = lean_string_append(v___x_3942_, v___x_3944_);
                            crate::leanh::lean_dec_ref(v___x_3944_);
                            v___x_3946_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
                            v___x_3947_ = lean_string_append(v___x_3945_, v___x_3946_);
                            v___x_3948_ = lean_io_error_to_string(v_a_3937_);
                            v___x_3949_ = lean_string_append(v___x_3947_, v___x_3948_);
                            crate::leanh::lean_dec_ref(v___x_3948_);
                            v___x_3950_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                            v___x_3951_ = lean_string_append(v___x_3949_, v___x_3950_);
                            v___x_3952_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__8), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_reportResult___closed__8_once), _init_l___private_Lake_Build_Run_0__Lake_reportResult___closed__8);
                            v___x_3953_ = lean_string_append(v___x_3951_, v___x_3952_);
                            v___x_3954_ = l_mkPanicMessageWithDecl(
                                v___x_3938_,
                                v___x_3939_,
                                v___x_3940_,
                                v___x_3941_,
                                v___x_3953_,
                            );
                            crate::leanh::lean_dec_ref(v___x_3953_);
                            v___x_3955_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_3954_);
                            return v___x_3955_;
                        }
                    }
                }
            }
            7 => {
                v___x_3962_ = crate::leanh::lean_apply_1(v_flush_3959_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_3962_) == 0 {
                    v_a_3963_ = crate::leanh::lean_ctor_get(v___x_3962_, 0);
                    crate::leanh::lean_inc(v_a_3963_);
                    crate::leanh::lean_dec_ref_known(v___x_3962_, 1);
                    return v_a_3963_;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3962_, 1);
                    v___x_3964_ = crate::leanh::lean_box(0);
                    return v___x_3964_;
                }
            }
            8 => {
                state = 7;
                continue;
            }
            9 => {
                v___x_3968_ = lean_nat_dec_lt(v___x_3957_, v___x_3956_);
                if v___x_3968_ == 0 {
                    crate::leanh::lean_dec_ref(v_failures_3920_);
                    crate::leanh::lean_dec_ref(v_out_3841_);
                    state = 7;
                    continue;
                } else {
                    v___x_3969_ = crate::leanh::lean_box(0);
                    v___x_3970_ = lean_nat_dec_le(v___x_3956_, v___x_3956_);
                    if v___x_3970_ == 0 {
                        if v___x_3968_ == 0 {
                            crate::leanh::lean_dec_ref(v_failures_3920_);
                            crate::leanh::lean_dec_ref(v_out_3841_);
                            state = 7;
                            continue;
                        } else {
                            v___x_3971_ = 0usize;
                            v___x_3972_ = lean_usize_of_nat(v___x_3956_);
                            v___x_3973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_3841_, v_failures_3920_, v___x_3971_, v___x_3972_, v___x_3969_);
                            crate::leanh::lean_dec_ref(v_failures_3920_);
                            v___y_3966_ = v___x_3973_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_3974_ = 0usize;
                        v___x_3975_ = lean_usize_of_nat(v___x_3956_);
                        v___x_3976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_reportResult_spec__0(v_out_3841_, v_failures_3920_, v___x_3974_, v___x_3975_, v___x_3969_);
                        crate::leanh::lean_dec_ref(v_failures_3920_);
                        v___y_3966_ = v___x_3976_;
                        state = 8;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_reportResult___boxed(
    mut v_cfg_3995_: *mut crate::leanh::LeanObject,
    mut v_out_3996_: *mut crate::leanh::LeanObject,
    mut v_result_3997_: *mut crate::leanh::LeanObject,
    mut v_a_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3999_ =
        l___private_Lake_Build_Run_0__Lake_reportResult(v_cfg_3995_, v_out_3996_, v_result_3997_);
    crate::leanh::lean_dec_ref(v_cfg_3995_);
    return v_res_3999_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(
    mut v_self_4000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toMonitorResult_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toMonitorResult_4001_ = crate::leanh::lean_ctor_get(v_self_4000_, 0);
    crate::leanh::lean_inc_ref(v_toMonitorResult_4001_);
    return v_toMonitorResult_4001_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0___boxed(
    mut v_self_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4003_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___lam__0(
        v_self_4002_,
    );
    crate::leanh::lean_dec_ref(v_self_4002_);
    return v_res_4003_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult(
    mut v_00_u03b1_4005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4006_ = l___private_Lake_Build_Run_0__Lake_instCoeOutBuildResultMonitorResult___closed__0;
    return v___f_4006_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(
    mut v_self_4007_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_out_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_out_4008_ = crate::leanh::lean_ctor_get(v_self_4007_, 1);
    if crate::leanh::lean_obj_tag(v_out_4008_) == 0 {
        let mut v___x_4009_: u8 = 0;
        v___x_4009_ = 0;
        return v___x_4009_;
    } else {
        let mut v___x_4010_: u8 = 0;
        v___x_4010_ = 1;
        return v___x_4010_;
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg___boxed(
    mut v_self_4011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4012_: u8 = 0;
    let mut v_r_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4012_ = l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___redArg(v_self_4011_);
    crate::leanh::lean_dec_ref(v_self_4011_);
    v_r_4013_ = crate::leanh::lean_box((v_res_4012_) as usize);
    return v_r_4013_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(
    mut v_00_u03b1_4014_: *mut crate::leanh::LeanObject,
    mut v_self_4015_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_out_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_out_4016_ = crate::leanh::lean_ctor_get(v_self_4015_, 1);
    if crate::leanh::lean_obj_tag(v_out_4016_) == 0 {
        let mut v___x_4017_: u8 = 0;
        v___x_4017_ = 0;
        return v___x_4017_;
    } else {
        let mut v___x_4018_: u8 = 0;
        v___x_4018_ = 1;
        return v___x_4018_;
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_BuildResult_isOk___boxed(
    mut v_00_u03b1_4019_: *mut crate::leanh::LeanObject,
    mut v_self_4020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4021_: u8 = 0;
    let mut v_r_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4021_ =
        l___private_Lake_Build_Run_0__Lake_BuildResult_isOk(v_00_u03b1_4019_, v_self_4020_);
    crate::leanh::lean_dec_ref(v_self_4020_);
    v_r_4022_ = crate::leanh::lean_box((v_res_4021_) as usize);
    return v_r_4022_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(
    mut v_ctx_4031_: *mut crate::leanh::LeanObject,
    mut v_job_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_failures_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: u8 = 0;
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4057_: u8 = 0;
    let mut v_unused_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4061_: u8 = 0;
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v_unused_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_job_4032_);
                v___x_4034_ = l_Lake_Job_toOpaque___redArg(v_job_4032_);
                v___x_4035_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4036_ = lean_mk_empty_array_with_capacity(v___x_4035_);
                v___x_4037_ = lean_array_push(v___x_4036_, v___x_4034_);
                v___x_4038_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4039_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__0;
                v___x_4040_ =
                    l___private_Lake_Build_Run_0__Lake_Monitor_renderProgress___redArg___closed__1;
                v___x_4041_ = l___private_Lake_Build_Run_0__Lake_monitorJobs_x27(
                    v_ctx_4031_,
                    v___x_4037_,
                    v___x_4039_,
                    v___x_4040_,
                );
                v_failures_4042_ = crate::leanh::lean_ctor_get(v___x_4041_, 0);
                crate::leanh::lean_inc_ref(v_failures_4042_);
                v___x_4043_ = lean_array_get_size(v_failures_4042_);
                crate::leanh::lean_dec_ref(v_failures_4042_);
                v___x_4044_ = lean_nat_dec_eq(v___x_4043_, v___x_4038_);
                if v___x_4044_ == 0 {
                    crate::leanh::lean_dec_ref(v_job_4032_);
                    v___x_4045_ =
                        l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__2;
                    v___x_4046_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4046_, 0, v___x_4041_);
                    crate::leanh::lean_ctor_set(v___x_4046_, 1, v___x_4045_);
                    return v___x_4046_;
                } else {
                    v_task_4047_ = crate::leanh::lean_ctor_get(v_job_4032_, 0);
                    crate::leanh::lean_inc_ref(v_task_4047_);
                    crate::leanh::lean_dec_ref(v_job_4032_);
                    v___x_4048_ = lean_io_wait(v_task_4047_);
                    if crate::leanh::lean_obj_tag(v___x_4048_) == 0 {
                        v_a_4049_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                        v_isSharedCheck_4057_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4048_)) as u8;
                        if v_isSharedCheck_4057_ == 0 {
                            v_unused_4058_ = crate::leanh::lean_ctor_get(v___x_4048_, 1);
                            crate::leanh::lean_dec(v_unused_4058_);
                            v___x_4051_ = v___x_4048_;
                            v_isShared_4052_ = v_isSharedCheck_4057_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4049_);
                            crate::leanh::lean_dec(v___x_4048_);
                            v___x_4051_ = crate::leanh::lean_box(0);
                            v_isShared_4052_ = v_isSharedCheck_4057_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_4066_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4048_)) as u8;
                        if v_isSharedCheck_4066_ == 0 {
                            v_unused_4067_ = crate::leanh::lean_ctor_get(v___x_4048_, 1);
                            crate::leanh::lean_dec(v_unused_4067_);
                            v_unused_4068_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                            crate::leanh::lean_dec(v_unused_4068_);
                            v___x_4060_ = v___x_4048_;
                            v_isShared_4061_ = v_isSharedCheck_4066_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4048_);
                            v___x_4060_ = crate::leanh::lean_box(0);
                            v_isShared_4061_ = v_isSharedCheck_4066_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4053_, 0, v_a_4049_);
                if v_isShared_4052_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4051_, 1, v___x_4053_);
                    crate::leanh::lean_ctor_set(v___x_4051_, 0, v___x_4041_);
                    v___x_4055_ = v___x_4051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___x_4053_);
                    v___x_4055_ = v_reuseFailAlloc_4056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4055_;
            }
            3 => {
                v___x_4062_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___closed__4;
                if v_isShared_4061_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4060_, 0);
                    crate::leanh::lean_ctor_set(v___x_4060_, 1, v___x_4062_);
                    crate::leanh::lean_ctor_set(v___x_4060_, 0, v___x_4041_);
                    v___x_4064_ = v___x_4060_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 1, v___x_4062_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorJob___redArg___boxed(
    mut v_ctx_4069_: *mut crate::leanh::LeanObject,
    mut v_job_4070_: *mut crate::leanh::LeanObject,
    mut v_a_4071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4072_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_4069_, v_job_4070_);
    crate::leanh::lean_dec_ref(v_ctx_4069_);
    return v_res_4072_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorJob(
    mut v_00_u03b1_4073_: *mut crate::leanh::LeanObject,
    mut v_ctx_4074_: *mut crate::leanh::LeanObject,
    mut v_job_4075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4077_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v_ctx_4074_, v_job_4075_);
    return v___x_4077_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorJob___boxed(
    mut v_00_u03b1_4078_: *mut crate::leanh::LeanObject,
    mut v_ctx_4079_: *mut crate::leanh::LeanObject,
    mut v_job_4080_: *mut crate::leanh::LeanObject,
    mut v_a_4081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4082_ =
        l___private_Lake_Build_Run_0__Lake_monitorJob(v_00_u03b1_4078_, v_ctx_4079_, v_job_4080_);
    crate::leanh::lean_dec_ref(v_ctx_4079_);
    return v_res_4082_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4085_ = crate::leanh::lean_box(0);
    v___x_4086_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4087_ = lean_mk_array(v___x_4086_, v___x_4085_);
    return v___x_4087_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4088_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1),
        core::ptr::addr_of_mut!(
            l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1_once
        ),
        _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__1,
    );
    v___x_4089_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4090_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4090_, 0, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4090_, 1, v___x_4088_);
    return v___x_4090_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(
    mut v_ws_4091_: *mut crate::leanh::LeanObject,
    mut v_cfg_4092_: *mut crate::leanh::LeanObject,
    mut v_jobs_4093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u64 = 0;
    let mut v___x_4100_: u64 = 0;
    let mut v___x_4101_: u64 = 0;
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_outputsFile_x3f_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4118_: u8 = 0;
    let mut v_unused_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outputsFile_x3f_4108_ = crate::leanh::lean_ctor_get(v_cfg_4092_, 1);
                crate::leanh::lean_inc(v_outputsFile_x3f_4108_);
                if crate::leanh::lean_obj_tag(v_outputsFile_x3f_4108_) == 0 {
                    v___x_4109_ = crate::leanh::lean_box(0);
                    v_val_4096_ = v___x_4109_;
                    state = 1;
                    continue;
                } else {
                    v_isSharedCheck_4118_ =
                        (!crate::leanh::lean_is_exclusive(v_outputsFile_x3f_4108_)) as u8;
                    if v_isSharedCheck_4118_ == 0 {
                        v_unused_4119_ = crate::leanh::lean_ctor_get(v_outputsFile_x3f_4108_, 0);
                        crate::leanh::lean_dec(v_unused_4119_);
                        v___x_4111_ = v_outputsFile_x3f_4108_;
                        v_isShared_4112_ = v_isSharedCheck_4118_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_outputsFile_x3f_4108_);
                        v___x_4111_ = crate::leanh::lean_box(0);
                        v_isShared_4112_ = v_isSharedCheck_4118_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_lakeEnv_4097_ = crate::leanh::lean_ctor_get(v_ws_4091_, 0);
                v___x_4098_ = l_Lake_Env_leanGithash(v_lakeEnv_4097_);
                v___x_4099_ = l_Lake_Hash_nil;
                v___x_4100_ = lean_string_hash(v___x_4098_);
                v___x_4101_ = lean_uint64_mix_hash(v___x_4099_, v___x_4100_);
                v___x_4102_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__4),
                    core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__4_once),
                    _init_l_Lake_mkBuildContext___closed__4,
                );
                v___x_4103_ = lean_string_append(v___x_4102_, v___x_4098_);
                crate::leanh::lean_dec_ref(v___x_4098_);
                v___x_4104_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__0;
                v___x_4105_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__6),
                    core::ptr::addr_of_mut!(l_Lake_mkBuildContext___closed__6_once),
                    _init_l_Lake_mkBuildContext___closed__6,
                );
                v___x_4106_ = crate::leanh::lean_alloc_ctor(0, 3, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_4106_, 0, v___x_4103_);
                crate::leanh::lean_ctor_set(v___x_4106_, 1, v___x_4104_);
                crate::leanh::lean_ctor_set(v___x_4106_, 2, v___x_4105_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_4106_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4101_,
                );
                v___x_4107_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4107_, 0, v_cfg_4092_);
                crate::leanh::lean_ctor_set(v___x_4107_, 1, v_ws_4091_);
                crate::leanh::lean_ctor_set(v___x_4107_, 2, v___x_4106_);
                crate::leanh::lean_ctor_set(v___x_4107_, 3, v_jobs_4093_);
                crate::leanh::lean_ctor_set(v___x_4107_, 4, v_val_4096_);
                return v___x_4107_;
            }
            2 => {
                v___x_4113_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2_once
                    ),
                    _init_l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___closed__2,
                );
                v___x_4114_ = lean_st_mk_ref(v___x_4113_);
                if v_isShared_4112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4111_, 0, v___x_4114_);
                    v___x_4116_ = v___x_4111_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4114_);
                    v___x_4116_ = v_reuseFailAlloc_4117_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_4096_ = v___x_4116_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27___boxed(
    mut v_ws_4120_: *mut crate::leanh::LeanObject,
    mut v_cfg_4121_: *mut crate::leanh::LeanObject,
    mut v_jobs_4122_: *mut crate::leanh::LeanObject,
    mut v_a_4123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4124_ = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(
        v_ws_4120_,
        v_cfg_4121_,
        v_jobs_4122_,
    );
    return v_res_4124_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(
    mut v_build_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4134_: u8 = 0;
    let mut v_wantsRebuild_4135_: u8 = 0;
    let mut v_trace_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4140_: u8 = 0;
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4146_: u8 = 0;
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4153_: u8 = 0;
    let mut v_a_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4158_: u8 = 0;
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4165_: u8 = 0;
    let mut v_isSharedCheck_4166_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_4133_ = crate::leanh::lean_ctor_get(v___y_4131_, 0);
                v_action_4134_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4131_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4135_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4131_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4136_ = crate::leanh::lean_ctor_get(v___y_4131_, 1);
                v_buildTime_4137_ = crate::leanh::lean_ctor_get(v___y_4131_, 2);
                v_isSharedCheck_4166_ = (!crate::leanh::lean_is_exclusive(v___y_4131_)) as u8;
                if v_isSharedCheck_4166_ == 0 {
                    v___x_4139_ = v___y_4131_;
                    v_isShared_4140_ = v_isSharedCheck_4166_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_4137_);
                    crate::leanh::lean_inc(v_trace_4136_);
                    crate::leanh::lean_inc(v_log_4133_);
                    crate::leanh::lean_dec(v___y_4131_);
                    v___x_4139_ = crate::leanh::lean_box(0);
                    v_isShared_4140_ = v_isSharedCheck_4166_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4141_ = crate::leanh::lean_apply_7(
                    v_build_4125_,
                    v___y_4126_,
                    v___y_4127_,
                    v___y_4128_,
                    v___y_4129_,
                    v___y_4130_,
                    v_log_4133_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4141_) == 0 {
                    v_a_4142_ = crate::leanh::lean_ctor_get(v___x_4141_, 0);
                    v_a_4143_ = crate::leanh::lean_ctor_get(v___x_4141_, 1);
                    v_isSharedCheck_4153_ = (!crate::leanh::lean_is_exclusive(v___x_4141_)) as u8;
                    if v_isSharedCheck_4153_ == 0 {
                        v___x_4145_ = v___x_4141_;
                        v_isShared_4146_ = v_isSharedCheck_4153_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4143_);
                        crate::leanh::lean_inc(v_a_4142_);
                        crate::leanh::lean_dec(v___x_4141_);
                        v___x_4145_ = crate::leanh::lean_box(0);
                        v_isShared_4146_ = v_isSharedCheck_4153_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4154_ = crate::leanh::lean_ctor_get(v___x_4141_, 0);
                    v_a_4155_ = crate::leanh::lean_ctor_get(v___x_4141_, 1);
                    v_isSharedCheck_4165_ = (!crate::leanh::lean_is_exclusive(v___x_4141_)) as u8;
                    if v_isSharedCheck_4165_ == 0 {
                        v___x_4157_ = v___x_4141_;
                        v_isShared_4158_ = v_isSharedCheck_4165_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4155_);
                        crate::leanh::lean_inc(v_a_4154_);
                        crate::leanh::lean_dec(v___x_4141_);
                        v___x_4157_ = crate::leanh::lean_box(0);
                        v_isShared_4158_ = v_isSharedCheck_4165_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4140_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4139_, 0, v_a_4143_);
                    v___x_4148_ = v___x_4139_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4152_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4152_, 1, v_trace_4136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4152_, 2, v_buildTime_4137_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4152_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4134_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4152_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4135_,
                    );
                    v___x_4148_ = v_reuseFailAlloc_4152_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4146_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4145_, 1, v___x_4148_);
                    v___x_4150_ = v___x_4145_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4151_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4142_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4151_, 1, v___x_4148_);
                    v___x_4150_ = v_reuseFailAlloc_4151_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4150_;
            }
            5 => {
                if v_isShared_4140_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4139_, 0, v_a_4155_);
                    v___x_4160_ = v___x_4139_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4164_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 1, v_trace_4136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 2, v_buildTime_4137_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4164_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4134_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4164_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4135_,
                    );
                    v___x_4160_ = v_reuseFailAlloc_4164_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4158_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4157_, 1, v___x_4160_);
                    v___x_4162_ = v___x_4157_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 1, v___x_4160_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed(
    mut v_build_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4175_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0(
        v_build_4167_,
        v___y_4168_,
        v___y_4169_,
        v___y_4170_,
        v___y_4171_,
        v___y_4172_,
        v___y_4173_,
    );
    return v_res_4175_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(
    mut v_bctx_4177_: *mut crate::leanh::LeanObject,
    mut v_build_4178_: *mut crate::leanh::LeanObject,
    mut v_caption_4179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4181_ = crate::leanh::lean_box(1);
    v___x_4182_ = lean_st_mk_ref(v___x_4181_);
    v___f_4183_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        8,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4183_, 0, v_build_4178_);
    v___x_4184_ = crate::leanh::lean_box(0);
    v___x_4185_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4186_ = crate::leanh::lean_box(0);
    v___x_4187_ = crate::leanh::lean_box(0);
    v___x_4188_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___closed__0;
    v___x_4189_ = l_Lake_Job_async___redArg(
        v___x_4184_,
        v___f_4183_,
        v___x_4185_,
        v_caption_4179_,
        v___x_4188_,
        v___x_4187_,
        v___x_4186_,
        v___x_4182_,
        v_bctx_4177_,
    );
    v___x_4190_ = lean_st_ref_get(v___x_4182_);
    crate::leanh::lean_dec(v___x_4182_);
    crate::leanh::lean_dec(v___x_4190_);
    return v___x_4189_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg___boxed(
    mut v_bctx_4191_: *mut crate::leanh::LeanObject,
    mut v_build_4192_: *mut crate::leanh::LeanObject,
    mut v_caption_4193_: *mut crate::leanh::LeanObject,
    mut v_a_4194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4195_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(
        v_bctx_4191_,
        v_build_4192_,
        v_caption_4193_,
    );
    crate::leanh::lean_dec_ref(v_bctx_4191_);
    return v_res_4195_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(
    mut v_00_u03b1_4196_: *mut crate::leanh::LeanObject,
    mut v_bctx_4197_: *mut crate::leanh::LeanObject,
    mut v_build_4198_: *mut crate::leanh::LeanObject,
    mut v_caption_4199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4201_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(
        v_bctx_4197_,
        v_build_4198_,
        v_caption_4199_,
    );
    return v___x_4201_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___boxed(
    mut v_00_u03b1_4202_: *mut crate::leanh::LeanObject,
    mut v_bctx_4203_: *mut crate::leanh::LeanObject,
    mut v_build_4204_: *mut crate::leanh::LeanObject,
    mut v_caption_4205_: *mut crate::leanh::LeanObject,
    mut v_a_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4207_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild(
        v_00_u03b1_4202_,
        v_bctx_4203_,
        v_build_4204_,
        v_caption_4205_,
    );
    crate::leanh::lean_dec_ref(v_bctx_4203_);
    return v_res_4207_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(
    mut v_x_4208_: *mut crate::leanh::LeanObject,
    mut v_x_4209_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4208_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4209_) == 0 {
            let mut v___x_4210_: u8 = 0;
            v___x_4210_ = 1;
            return v___x_4210_;
        } else {
            let mut v___x_4211_: u8 = 0;
            v___x_4211_ = 0;
            return v___x_4211_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4209_) == 0 {
            let mut v___x_4212_: u8 = 0;
            v___x_4212_ = 0;
            return v___x_4212_;
        } else {
            let mut v_val_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4214_: u8 = 0;
            v_val_4213_ = crate::leanh::lean_ctor_get(v_x_4208_, 0);
            v___x_4214_ = (crate::leanh::lean_unbox(v_val_4213_) as u8);
            if v___x_4214_ == 0 {
                let mut v_val_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4216_: u8 = 0;
                v_val_4215_ = crate::leanh::lean_ctor_get(v_x_4209_, 0);
                v___x_4216_ = (crate::leanh::lean_unbox(v_val_4215_) as u8);
                if v___x_4216_ == 0 {
                    let mut v___x_4217_: u8 = 0;
                    v___x_4217_ = 1;
                    return v___x_4217_;
                } else {
                    let mut v___x_4218_: u8 = 0;
                    v___x_4218_ = (crate::leanh::lean_unbox(v_val_4213_) as u8);
                    return v___x_4218_;
                }
            } else {
                let mut v_val_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4220_: u8 = 0;
                v_val_4219_ = crate::leanh::lean_ctor_get(v_x_4209_, 0);
                v___x_4220_ = (crate::leanh::lean_unbox(v_val_4219_) as u8);
                return v___x_4220_;
            }
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0___boxed(
    mut v_x_4221_: *mut crate::leanh::LeanObject,
    mut v_x_4222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4223_: u8 = 0;
    let mut v_r_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4223_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_x_4221_, v_x_4222_);
    crate::leanh::lean_dec(v_x_4222_);
    crate::leanh::lean_dec(v_x_4221_);
    v_r_4224_ = crate::leanh::lean_box((v_res_4223_) as usize);
    return v_r_4224_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(
    mut v___x_4225_: *mut crate::leanh::LeanObject,
    mut v___x_4226_: u8,
    mut v___x_4227_: u8,
    mut v_as_4228_: *mut crate::leanh::LeanObject,
    mut v_i_4229_: usize,
    mut v_stop_4230_: usize,
    mut v_b_4231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4233_: u8 = 0;
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: usize = 0;
    let mut v___x_4237_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4233_ = lean_usize_dec_eq(v_i_4229_, v_stop_4230_);
                if v___x_4233_ == 0 {
                    v___x_4234_ = lean_array_uget_borrowed(v_as_4228_, v_i_4229_);
                    crate::leanh::lean_inc_ref(v___x_4225_);
                    v___x_4235_ =
                        l_Lake_logToStream(v___x_4234_, v___x_4225_, v___x_4226_, v___x_4227_);
                    v___x_4236_ = 1usize;
                    v___x_4237_ = lean_usize_add(v_i_4229_, v___x_4236_);
                    v_i_4229_ = v___x_4237_;
                    v_b_4231_ = v___x_4235_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_4225_);
                    return v_b_4231_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1___boxed(
    mut v___x_4239_: *mut crate::leanh::LeanObject,
    mut v___x_4240_: *mut crate::leanh::LeanObject,
    mut v___x_4241_: *mut crate::leanh::LeanObject,
    mut v_as_4242_: *mut crate::leanh::LeanObject,
    mut v_i_4243_: *mut crate::leanh::LeanObject,
    mut v_stop_4244_: *mut crate::leanh::LeanObject,
    mut v_b_4245_: *mut crate::leanh::LeanObject,
    mut v___y_4246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1083__boxed_4247_: u8 = 0;
    let mut v___x_1084__boxed_4248_: u8 = 0;
    let mut v_i_boxed_4249_: usize = 0;
    let mut v_stop_boxed_4250_: usize = 0;
    let mut v_res_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1083__boxed_4247_ = (crate::leanh::lean_unbox(v___x_4240_) as u8);
    v___x_1084__boxed_4248_ = (crate::leanh::lean_unbox(v___x_4241_) as u8);
    v_i_boxed_4249_ = crate::leanh::lean_unbox_usize(v_i_4243_);
    crate::leanh::lean_dec(v_i_4243_);
    v_stop_boxed_4250_ = crate::leanh::lean_unbox_usize(v_stop_4244_);
    crate::leanh::lean_dec(v_stop_4244_);
    v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_4239_, v___x_1083__boxed_4247_, v___x_1084__boxed_4248_, v_as_4242_, v_i_boxed_4249_, v_stop_boxed_4250_, v_b_4245_);
    crate::leanh::lean_dec_ref(v_as_4242_);
    return v_res_4251_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(
    mut v___x_4252_: *mut crate::leanh::LeanObject,
    mut v___x_4253_: u8,
    mut v___x_4254_: u8,
    mut v_ws_4255_: *mut crate::leanh::LeanObject,
    mut v_outputsRef_x3f_4256_: *mut crate::leanh::LeanObject,
    mut v_out_4257_: *mut crate::leanh::LeanObject,
    mut v_outputsFile_4258_: *mut crate::leanh::LeanObject,
    mut v_isVerbose_4259_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    let mut v___x_4269_: u8 = 0;
    let mut v___x_4270_: usize = 0;
    let mut v___x_4271_: usize = 0;
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: usize = 0;
    let mut v___x_4274_: usize = 0;
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: u8 = 0;
    let mut v___x_4283_: u8 = 0;
    let mut v___x_4284_: usize = 0;
    let mut v___x_4285_: usize = 0;
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: usize = 0;
    let mut v___x_4288_: usize = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: u8 = 0;
    let mut v_putStr_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v_packages_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: u8 = 0;
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4364_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_4255_);
                if v___x_4364_ == 0 {
                    v_packages_4365_ = crate::leanh::lean_ctor_get(v_ws_4255_, 4);
                    v___x_4366_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4367_ = lean_array_fget_borrowed(v_packages_4365_, v___x_4366_);
                    v_baseName_4368_ = crate::leanh::lean_ctor_get(v___x_4367_, 1);
                    crate::leanh::lean_inc(v_baseName_4368_);
                    v___x_4369_ = l_Lean_Name_toString(v_baseName_4368_, v___x_4364_);
                    v___x_4370_ =
                        l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__15;
                    v___x_4371_ = lean_string_append(v___x_4369_, v___x_4370_);
                    v___x_4372_ = 2;
                    v___x_4373_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4373_, 0, v___x_4371_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4373_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_4372_,
                    );
                    crate::leanh::lean_inc_ref(v___x_4252_);
                    v___x_4374_ =
                        l_Lake_logToStream(v___x_4373_, v___x_4252_, v___x_4253_, v___x_4254_);
                    crate::leanh::lean_dec_ref_known(v___x_4373_, 1);
                    state = 4;
                    continue;
                } else {
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_4262_ = crate::leanh::lean_box(0);
                return v___x_4262_;
            }
            2 => {
                v___x_4266_ = lean_array_get_size(v___y_4264_);
                v___x_4267_ = crate::leanh::lean_box(0);
                v___x_4268_ = lean_nat_dec_lt(v___y_4265_, v___x_4266_);
                if v___x_4268_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4264_);
                    crate::leanh::lean_dec_ref(v___x_4252_);
                    return v___x_4267_;
                } else {
                    v___x_4269_ = lean_nat_dec_le(v___x_4266_, v___x_4266_);
                    if v___x_4269_ == 0 {
                        if v___x_4268_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_4264_);
                            crate::leanh::lean_dec_ref(v___x_4252_);
                            return v___x_4267_;
                        } else {
                            v___x_4270_ = 0usize;
                            v___x_4271_ = lean_usize_of_nat(v___x_4266_);
                            v___x_4272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_4252_, v___x_4253_, v___x_4254_, v___y_4264_, v___x_4270_, v___x_4271_, v___x_4267_);
                            crate::leanh::lean_dec_ref(v___y_4264_);
                            return v___x_4272_;
                        }
                    } else {
                        v___x_4273_ = 0usize;
                        v___x_4274_ = lean_usize_of_nat(v___x_4266_);
                        v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_4252_, v___x_4253_, v___x_4254_, v___y_4264_, v___x_4273_, v___x_4274_, v___x_4267_);
                        crate::leanh::lean_dec_ref(v___y_4264_);
                        return v___x_4275_;
                    }
                }
            }
            3 => {
                if v_isVerbose_4259_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4277_);
                    crate::leanh::lean_dec_ref(v___x_4252_);
                    v___x_4279_ = crate::leanh::lean_box(0);
                    return v___x_4279_;
                } else {
                    v___x_4280_ = lean_array_get_size(v___y_4277_);
                    v___x_4281_ = crate::leanh::lean_box(0);
                    v___x_4282_ = lean_nat_dec_lt(v___y_4278_, v___x_4280_);
                    if v___x_4282_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_4277_);
                        crate::leanh::lean_dec_ref(v___x_4252_);
                        return v___x_4281_;
                    } else {
                        v___x_4283_ = lean_nat_dec_le(v___x_4280_, v___x_4280_);
                        if v___x_4283_ == 0 {
                            if v___x_4282_ == 0 {
                                crate::leanh::lean_dec_ref(v___y_4277_);
                                crate::leanh::lean_dec_ref(v___x_4252_);
                                return v___x_4281_;
                            } else {
                                v___x_4284_ = 0usize;
                                v___x_4285_ = lean_usize_of_nat(v___x_4280_);
                                v___x_4286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_4252_, v___x_4253_, v___x_4254_, v___y_4277_, v___x_4284_, v___x_4285_, v___x_4281_);
                                crate::leanh::lean_dec_ref(v___y_4277_);
                                return v___x_4286_;
                            }
                        } else {
                            v___x_4287_ = 0usize;
                            v___x_4288_ = lean_usize_of_nat(v___x_4280_);
                            v___x_4289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__1(v___x_4252_, v___x_4253_, v___x_4254_, v___y_4277_, v___x_4287_, v___x_4288_, v___x_4281_);
                            crate::leanh::lean_dec_ref(v___y_4277_);
                            return v___x_4289_;
                        }
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_outputsRef_x3f_4256_) == 1 {
                    v_val_4291_ = crate::leanh::lean_ctor_get(v_outputsRef_x3f_4256_, 0);
                    v___x_4292_ = lean_st_ref_get(v_val_4291_);
                    v_packages_4293_ = crate::leanh::lean_ctor_get(v_ws_4255_, 4);
                    v___x_4294_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4295_ = lean_array_fget_borrowed(v_packages_4293_, v___x_4294_);
                    v_config_4296_ = crate::leanh::lean_ctor_get(v___x_4295_, 6);
                    v_toLeanConfig_4297_ = crate::leanh::lean_ctor_get(v_config_4296_, 1);
                    v_platformIndependent_4298_ =
                        crate::leanh::lean_ctor_get(v_toLeanConfig_4297_, 10);
                    v___x_4299_ =
                        l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__1;
                    v___x_4300_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0_spec__0(v_platformIndependent_4298_, v___x_4299_);
                    v___x_4301_ =
                        l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__2;
                    v___x_4302_ = l_Lake_CacheMap_writeFile(
                        v_outputsFile_4258_,
                        v___x_4292_,
                        v___x_4300_,
                        v___x_4301_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4302_) == 0 {
                        v_a_4303_ = crate::leanh::lean_ctor_get(v___x_4302_, 1);
                        crate::leanh::lean_inc(v_a_4303_);
                        crate::leanh::lean_dec_ref_known(v___x_4302_, 2);
                        v___x_4304_ = lean_array_get_size(v_a_4303_);
                        v___x_4305_ = lean_nat_dec_eq(v___x_4304_, v___x_4294_);
                        if v___x_4305_ == 0 {
                            if v_isVerbose_4259_ == 0 {
                                crate::leanh::lean_dec(v_a_4303_);
                                crate::leanh::lean_dec_ref(v_out_4257_);
                                crate::leanh::lean_dec_ref(v___x_4252_);
                                state = 1;
                                continue;
                            } else {
                                v_putStr_4306_ = crate::leanh::lean_ctor_get(v_out_4257_, 4);
                                crate::leanh::lean_inc_ref(v_putStr_4306_);
                                crate::leanh::lean_dec_ref(v_out_4257_);
                                v___x_4307_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__3;
                                v___x_4308_ = crate::leanh::lean_apply_2(
                                    v_putStr_4306_,
                                    v___x_4307_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_4308_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4308_, 1);
                                    v___y_4264_ = v_a_4303_;
                                    v___y_4265_ = v___x_4294_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_4309_ = crate::leanh::lean_ctor_get(v___x_4308_, 0);
                                    crate::leanh::lean_inc(v_a_4309_);
                                    crate::leanh::lean_dec_ref_known(v___x_4308_, 1);
                                    v___x_4310_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                                    v___x_4311_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                                    v___x_4312_ = crate::leanh::lean_unsigned_to_nat(89);
                                    v___x_4313_ = crate::leanh::lean_unsigned_to_nat(4);
                                    v___x_4314_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__3;
                                    v___x_4315_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__15;
                                    v___x_4316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4315_, v_isVerbose_4259_);
                                    v___x_4317_ = lean_string_append(v___x_4314_, v___x_4316_);
                                    crate::leanh::lean_dec_ref(v___x_4316_);
                                    v___x_4318_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__18;
                                    v___x_4319_ = lean_string_append(v___x_4317_, v___x_4318_);
                                    v___x_4320_ = lean_io_error_to_string(v_a_4309_);
                                    v___x_4321_ = lean_string_append(v___x_4319_, v___x_4320_);
                                    crate::leanh::lean_dec_ref(v___x_4320_);
                                    v___x_4322_ =
                                        l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                                    v___x_4323_ = lean_string_append(v___x_4321_, v___x_4322_);
                                    v___x_4324_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6_once), _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__6);
                                    v___x_4325_ = lean_string_append(v___x_4323_, v___x_4324_);
                                    v___x_4326_ = l_mkPanicMessageWithDecl(
                                        v___x_4310_,
                                        v___x_4311_,
                                        v___x_4312_,
                                        v___x_4313_,
                                        v___x_4325_,
                                    );
                                    crate::leanh::lean_dec_ref(v___x_4325_);
                                    v___x_4327_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_4326_);
                                    v___y_4264_ = v_a_4303_;
                                    v___y_4265_ = v___x_4294_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4303_);
                            crate::leanh::lean_dec_ref(v_out_4257_);
                            crate::leanh::lean_dec_ref(v___x_4252_);
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4328_ = crate::leanh::lean_ctor_get(v___x_4302_, 1);
                        crate::leanh::lean_inc(v_a_4328_);
                        crate::leanh::lean_dec_ref_known(v___x_4302_, 2);
                        v_putStr_4329_ = crate::leanh::lean_ctor_get(v_out_4257_, 4);
                        crate::leanh::lean_inc_ref(v_putStr_4329_);
                        crate::leanh::lean_dec_ref(v_out_4257_);
                        v___x_4330_ =
                            l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__7;
                        v___x_4331_ = crate::leanh::lean_apply_2(
                            v_putStr_4329_,
                            v___x_4330_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4331_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4331_, 1);
                            v___y_4277_ = v_a_4328_;
                            v___y_4278_ = v___x_4294_;
                            state = 3;
                            continue;
                        } else {
                            v_a_4332_ = crate::leanh::lean_ctor_get(v___x_4331_, 0);
                            crate::leanh::lean_inc(v_a_4332_);
                            crate::leanh::lean_dec_ref_known(v___x_4331_, 1);
                            v___x_4333_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                            v___x_4334_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                            v___x_4335_ = crate::leanh::lean_unsigned_to_nat(89);
                            v___x_4336_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_4337_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_Build_Run_0__Lake_print_x21___closed__19
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once
                                ),
                                _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19,
                            );
                            v___x_4338_ = lean_io_error_to_string(v_a_4332_);
                            v___x_4339_ = lean_string_append(v___x_4337_, v___x_4338_);
                            crate::leanh::lean_dec_ref(v___x_4338_);
                            v___x_4340_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                            v___x_4341_ = lean_string_append(v___x_4339_, v___x_4340_);
                            v___x_4342_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10_once), _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__10);
                            v___x_4343_ = lean_string_append(v___x_4341_, v___x_4342_);
                            v___x_4344_ = l_mkPanicMessageWithDecl(
                                v___x_4333_,
                                v___x_4334_,
                                v___x_4335_,
                                v___x_4336_,
                                v___x_4343_,
                            );
                            crate::leanh::lean_dec_ref(v___x_4343_);
                            v___x_4345_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_4344_);
                            v___y_4277_ = v_a_4328_;
                            v___y_4278_ = v___x_4294_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_outputsFile_4258_);
                    crate::leanh::lean_dec_ref(v___x_4252_);
                    v_putStr_4346_ = crate::leanh::lean_ctor_get(v_out_4257_, 4);
                    crate::leanh::lean_inc_ref(v_putStr_4346_);
                    crate::leanh::lean_dec_ref(v_out_4257_);
                    v___x_4347_ =
                        l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__11;
                    v___x_4348_ = crate::leanh::lean_apply_2(
                        v_putStr_4346_,
                        v___x_4347_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4348_) == 0 {
                        v_a_4349_ = crate::leanh::lean_ctor_get(v___x_4348_, 0);
                        crate::leanh::lean_inc(v_a_4349_);
                        crate::leanh::lean_dec_ref_known(v___x_4348_, 1);
                        return v_a_4349_;
                    } else {
                        v_a_4350_ = crate::leanh::lean_ctor_get(v___x_4348_, 0);
                        crate::leanh::lean_inc(v_a_4350_);
                        crate::leanh::lean_dec_ref_known(v___x_4348_, 1);
                        v___x_4351_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__1;
                        v___x_4352_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__2;
                        v___x_4353_ = crate::leanh::lean_unsigned_to_nat(89);
                        v___x_4354_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_4355_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_print_x21___closed__19
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_Build_Run_0__Lake_print_x21___closed__19_once
                            ),
                            _init_l___private_Lake_Build_Run_0__Lake_print_x21___closed__19,
                        );
                        v___x_4356_ = lean_io_error_to_string(v_a_4350_);
                        v___x_4357_ = lean_string_append(v___x_4355_, v___x_4356_);
                        crate::leanh::lean_dec_ref(v___x_4356_);
                        v___x_4358_ = l___private_Lake_Build_Run_0__Lake_print_x21___closed__20;
                        v___x_4359_ = lean_string_append(v___x_4357_, v___x_4358_);
                        v___x_4360_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14_once), _init_l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___closed__14);
                        v___x_4361_ = lean_string_append(v___x_4359_, v___x_4360_);
                        v___x_4362_ = l_mkPanicMessageWithDecl(
                            v___x_4351_,
                            v___x_4352_,
                            v___x_4353_,
                            v___x_4354_,
                            v___x_4361_,
                        );
                        crate::leanh::lean_dec_ref(v___x_4361_);
                        v___x_4363_ = l_panic___at___00__private_Lake_Build_Run_0__Lake_Monitor_renderProgress_spec__0(v___x_4362_);
                        return v___x_4363_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0___boxed(
    mut v___x_4375_: *mut crate::leanh::LeanObject,
    mut v___x_4376_: *mut crate::leanh::LeanObject,
    mut v___x_4377_: *mut crate::leanh::LeanObject,
    mut v_ws_4378_: *mut crate::leanh::LeanObject,
    mut v_outputsRef_x3f_4379_: *mut crate::leanh::LeanObject,
    mut v_out_4380_: *mut crate::leanh::LeanObject,
    mut v_outputsFile_4381_: *mut crate::leanh::LeanObject,
    mut v_isVerbose_4382_: *mut crate::leanh::LeanObject,
    mut v_a_4383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1253__boxed_4384_: u8 = 0;
    let mut v___x_1254__boxed_4385_: u8 = 0;
    let mut v_isVerbose_boxed_4386_: u8 = 0;
    let mut v_res_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1253__boxed_4384_ = (crate::leanh::lean_unbox(v___x_4376_) as u8);
    v___x_1254__boxed_4385_ = (crate::leanh::lean_unbox(v___x_4377_) as u8);
    v_isVerbose_boxed_4386_ = (crate::leanh::lean_unbox(v_isVerbose_4382_) as u8);
    v_res_4387_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v___x_4375_, v___x_1253__boxed_4384_, v___x_1254__boxed_4385_, v_ws_4378_, v_outputsRef_x3f_4379_, v_out_4380_, v_outputsFile_4381_, v_isVerbose_boxed_4386_);
    crate::leanh::lean_dec(v_outputsRef_x3f_4379_);
    crate::leanh::lean_dec_ref(v_ws_4378_);
    return v_res_4387_;
}
pub unsafe fn _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0() -> u8 {
    let mut v___x_4388_: u32 = 0;
    let mut v___x_4389_: u8 = 0;
    v___x_4388_ = 3;
    v___x_4389_ = lean_uint32_to_uint8(v___x_4388_);
    return v___x_4389_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(
    mut v_cfg_4390_: *mut crate::leanh::LeanObject,
    mut v_bctx_4391_: *mut crate::leanh::LeanObject,
    mut v_mctx_4392_: *mut crate::leanh::LeanObject,
    mut v_result_4393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_outLv_4400_: u8 = 0;
    let mut v_useAnsi_4401_: u8 = 0;
    let mut v_toMonitorResult_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noBuild_4405_: u8 = 0;
    let mut v_verbosity_4406_: u8 = 0;
    let mut v_outputsFile_x3f_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wantsRebuild_4410_: u8 = 0;
    let mut v_a_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4417_: u8 = 0;
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut v_val_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_outputsRef_x3f_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4426_: u8 = 0;
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: u8 = 0;
    let mut v___x_4429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_out_4399_ = crate::leanh::lean_ctor_get(v_mctx_4392_, 1);
                crate::leanh::lean_inc_ref_n(v_out_4399_, 2);
                v_outLv_4400_ = crate::leanh::lean_ctor_get_uint8(
                    v_mctx_4392_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_useAnsi_4401_ = crate::leanh::lean_ctor_get_uint8(
                    v_mctx_4392_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v_mctx_4392_);
                v_toMonitorResult_4402_ = crate::leanh::lean_ctor_get(v_result_4393_, 0);
                crate::leanh::lean_inc_ref_n(v_toMonitorResult_4402_, 2);
                v_out_4403_ = crate::leanh::lean_ctor_get(v_result_4393_, 1);
                crate::leanh::lean_inc_ref(v_out_4403_);
                crate::leanh::lean_dec_ref(v_result_4393_);
                v___x_4404_ = l___private_Lake_Build_Run_0__Lake_reportResult(
                    v_cfg_4390_,
                    v_out_4399_,
                    v_toMonitorResult_4402_,
                );
                v_noBuild_4405_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_4390_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_verbosity_4406_ = crate::leanh::lean_ctor_get_uint8(
                    v_cfg_4390_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                );
                v_outputsFile_x3f_4407_ = crate::leanh::lean_ctor_get(v_cfg_4390_, 1);
                crate::leanh::lean_inc(v_outputsFile_x3f_4407_);
                crate::leanh::lean_dec_ref(v_cfg_4390_);
                if crate::leanh::lean_obj_tag(v_outputsFile_x3f_4407_) == 1 {
                    v_val_4422_ = crate::leanh::lean_ctor_get(v_outputsFile_x3f_4407_, 0);
                    crate::leanh::lean_inc(v_val_4422_);
                    crate::leanh::lean_dec_ref_known(v_outputsFile_x3f_4407_, 1);
                    v_toContext_4423_ = crate::leanh::lean_ctor_get(v_bctx_4391_, 1);
                    v_outputsRef_x3f_4424_ = crate::leanh::lean_ctor_get(v_bctx_4391_, 4);
                    if v_verbosity_4406_ == 2 {
                        v___x_4428_ = 1;
                        v___y_4426_ = v___x_4428_;
                        state = 5;
                        continue;
                    } else {
                        v___x_4429_ = 0;
                        v___y_4426_ = v___x_4429_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_outputsFile_x3f_4407_);
                    crate::leanh::lean_dec_ref(v_out_4399_);
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4397_ = lean_mk_io_user_error(v___y_4396_);
                v___x_4398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4398_, 0, v___x_4397_);
                return v___x_4398_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_out_4403_) == 0 {
                    if v_noBuild_4405_ == 0 {
                        crate::leanh::lean_dec_ref(v_toMonitorResult_4402_);
                        v_a_4409_ = crate::leanh::lean_ctor_get(v_out_4403_, 0);
                        crate::leanh::lean_inc(v_a_4409_);
                        crate::leanh::lean_dec_ref_known(v_out_4403_, 1);
                        v___y_4396_ = v_a_4409_;
                        state = 1;
                        continue;
                    } else {
                        v_wantsRebuild_4410_ = crate::leanh::lean_ctor_get_uint8(
                            v_toMonitorResult_4402_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        crate::leanh::lean_dec_ref(v_toMonitorResult_4402_);
                        if v_wantsRebuild_4410_ == 0 {
                            v_a_4411_ = crate::leanh::lean_ctor_get(v_out_4403_, 0);
                            crate::leanh::lean_inc(v_a_4411_);
                            crate::leanh::lean_dec_ref_known(v_out_4403_, 1);
                            v___y_4396_ = v_a_4411_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_out_4403_, 1);
                            v___x_4412_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0_once), _init_l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___closed__0);
                            v___x_4413_ = lean_io_exit(v___x_4412_);
                            return v___x_4413_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_toMonitorResult_4402_);
                    v_a_4414_ = crate::leanh::lean_ctor_get(v_out_4403_, 0);
                    v_isSharedCheck_4421_ = (!crate::leanh::lean_is_exclusive(v_out_4403_)) as u8;
                    if v_isSharedCheck_4421_ == 0 {
                        v___x_4416_ = v_out_4403_;
                        v_isShared_4417_ = v_isSharedCheck_4421_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4414_);
                        crate::leanh::lean_dec(v_out_4403_);
                        v___x_4416_ = crate::leanh::lean_box(0);
                        v_isShared_4417_ = v_isSharedCheck_4421_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4417_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4416_, 0);
                    v___x_4419_ = v___x_4416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4420_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
                    v___x_4419_ = v_reuseFailAlloc_4420_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4419_;
            }
            5 => {
                crate::leanh::lean_inc_ref(v_out_4399_);
                v___x_4427_ = l___private_Lake_Build_Run_0__Lake_Workspace_saveOutputs___at___00__private_Lake_Build_Run_0__Lake_finalizeBuild_spec__0(v_out_4399_, v_outLv_4400_, v_useAnsi_4401_, v_toContext_4423_, v_outputsRef_x3f_4424_, v_out_4399_, v_val_4422_, v___y_4426_);
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg___boxed(
    mut v_cfg_4430_: *mut crate::leanh::LeanObject,
    mut v_bctx_4431_: *mut crate::leanh::LeanObject,
    mut v_mctx_4432_: *mut crate::leanh::LeanObject,
    mut v_result_4433_: *mut crate::leanh::LeanObject,
    mut v_a_4434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4435_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(
        v_cfg_4430_,
        v_bctx_4431_,
        v_mctx_4432_,
        v_result_4433_,
    );
    crate::leanh::lean_dec_ref(v_bctx_4431_);
    return v_res_4435_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_finalizeBuild(
    mut v_00_u03b1_4436_: *mut crate::leanh::LeanObject,
    mut v_cfg_4437_: *mut crate::leanh::LeanObject,
    mut v_bctx_4438_: *mut crate::leanh::LeanObject,
    mut v_mctx_4439_: *mut crate::leanh::LeanObject,
    mut v_result_4440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4442_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(
        v_cfg_4437_,
        v_bctx_4438_,
        v_mctx_4439_,
        v_result_4440_,
    );
    return v___x_4442_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_finalizeBuild___boxed(
    mut v_00_u03b1_4443_: *mut crate::leanh::LeanObject,
    mut v_cfg_4444_: *mut crate::leanh::LeanObject,
    mut v_bctx_4445_: *mut crate::leanh::LeanObject,
    mut v_mctx_4446_: *mut crate::leanh::LeanObject,
    mut v_result_4447_: *mut crate::leanh::LeanObject,
    mut v_a_4448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4449_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild(
        v_00_u03b1_4443_,
        v_cfg_4444_,
        v_bctx_4445_,
        v_mctx_4446_,
        v_result_4447_,
    );
    crate::leanh::lean_dec_ref(v_bctx_4445_);
    return v_res_4449_;
}
pub unsafe fn l_Lake_Workspace_runFetchM___redArg(
    mut v_ws_4450_: *mut crate::leanh::LeanObject,
    mut v_build_4451_: *mut crate::leanh::LeanObject,
    mut v_cfg_4452_: *mut crate::leanh::LeanObject,
    mut v_caption_4453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = l_Lake_mkBuildContext___closed__0;
    v___x_4456_ = lean_st_mk_ref(v___x_4455_);
    crate::leanh::lean_inc(v___x_4456_);
    v___x_4457_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_4452_, v___x_4456_);
    crate::leanh::lean_inc_ref(v_cfg_4452_);
    v___x_4458_ =
        l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_4450_, v_cfg_4452_, v___x_4456_);
    v___x_4459_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(
        v___x_4458_,
        v_build_4451_,
        v_caption_4453_,
    );
    v___x_4460_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(v___x_4457_, v___x_4459_);
    v___x_4461_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(
        v_cfg_4452_,
        v___x_4458_,
        v___x_4457_,
        v___x_4460_,
    );
    crate::leanh::lean_dec_ref(v___x_4458_);
    return v___x_4461_;
}
pub unsafe fn l_Lake_Workspace_runFetchM___redArg___boxed(
    mut v_ws_4462_: *mut crate::leanh::LeanObject,
    mut v_build_4463_: *mut crate::leanh::LeanObject,
    mut v_cfg_4464_: *mut crate::leanh::LeanObject,
    mut v_caption_4465_: *mut crate::leanh::LeanObject,
    mut v_a_4466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4467_ = l_Lake_Workspace_runFetchM___redArg(
        v_ws_4462_,
        v_build_4463_,
        v_cfg_4464_,
        v_caption_4465_,
    );
    return v_res_4467_;
}
pub unsafe fn l_Lake_Workspace_runFetchM(
    mut v_00_u03b1_4468_: *mut crate::leanh::LeanObject,
    mut v_ws_4469_: *mut crate::leanh::LeanObject,
    mut v_build_4470_: *mut crate::leanh::LeanObject,
    mut v_cfg_4471_: *mut crate::leanh::LeanObject,
    mut v_caption_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Lake_Workspace_runFetchM___redArg(
        v_ws_4469_,
        v_build_4470_,
        v_cfg_4471_,
        v_caption_4472_,
    );
    return v___x_4474_;
}
pub unsafe fn l_Lake_Workspace_runFetchM___boxed(
    mut v_00_u03b1_4475_: *mut crate::leanh::LeanObject,
    mut v_ws_4476_: *mut crate::leanh::LeanObject,
    mut v_build_4477_: *mut crate::leanh::LeanObject,
    mut v_cfg_4478_: *mut crate::leanh::LeanObject,
    mut v_caption_4479_: *mut crate::leanh::LeanObject,
    mut v_a_4480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4481_ = l_Lake_Workspace_runFetchM(
        v_00_u03b1_4475_,
        v_ws_4476_,
        v_build_4477_,
        v_cfg_4478_,
        v_caption_4479_,
    );
    return v_res_4481_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(
    mut v_mctx_4485_: *mut crate::leanh::LeanObject,
    mut v_job_4486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonitorResult_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4493_: u8 = 0;
    let mut v_a_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4497_: u8 = 0;
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut v_unused_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v_toMonitorResult_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4514_: u8 = 0;
    let mut v_task_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut v_unused_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4488_ = l___private_Lake_Build_Run_0__Lake_monitorJob___redArg(
                    v_mctx_4485_,
                    v_job_4486_,
                );
                v_out_4489_ = crate::leanh::lean_ctor_get(v___x_4488_, 1);
                crate::leanh::lean_inc_ref(v_out_4489_);
                if crate::leanh::lean_obj_tag(v_out_4489_) == 0 {
                    v_toMonitorResult_4490_ = crate::leanh::lean_ctor_get(v___x_4488_, 0);
                    v_isSharedCheck_4505_ = (!crate::leanh::lean_is_exclusive(v___x_4488_)) as u8;
                    if v_isSharedCheck_4505_ == 0 {
                        v_unused_4506_ = crate::leanh::lean_ctor_get(v___x_4488_, 1);
                        crate::leanh::lean_dec(v_unused_4506_);
                        v___x_4492_ = v___x_4488_;
                        v_isShared_4493_ = v_isSharedCheck_4505_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_toMonitorResult_4490_);
                        crate::leanh::lean_dec(v___x_4488_);
                        v___x_4492_ = crate::leanh::lean_box(0);
                        v_isShared_4493_ = v_isSharedCheck_4505_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4507_ = crate::leanh::lean_ctor_get(v_out_4489_, 0);
                    v_isSharedCheck_4530_ = (!crate::leanh::lean_is_exclusive(v_out_4489_)) as u8;
                    if v_isSharedCheck_4530_ == 0 {
                        v___x_4509_ = v_out_4489_;
                        v_isShared_4510_ = v_isSharedCheck_4530_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4507_);
                        crate::leanh::lean_dec(v_out_4489_);
                        v___x_4509_ = crate::leanh::lean_box(0);
                        v_isShared_4510_ = v_isSharedCheck_4530_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4494_ = crate::leanh::lean_ctor_get(v_out_4489_, 0);
                v_isSharedCheck_4504_ = (!crate::leanh::lean_is_exclusive(v_out_4489_)) as u8;
                if v_isSharedCheck_4504_ == 0 {
                    v___x_4496_ = v_out_4489_;
                    v_isShared_4497_ = v_isSharedCheck_4504_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4494_);
                    crate::leanh::lean_dec(v_out_4489_);
                    v___x_4496_ = crate::leanh::lean_box(0);
                    v_isShared_4497_ = v_isSharedCheck_4504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4497_ == 0 {
                    v___x_4499_ = v___x_4496_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4494_);
                    v___x_4499_ = v_reuseFailAlloc_4503_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4493_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4492_, 1, v___x_4499_);
                    v___x_4501_ = v___x_4492_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4502_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_toMonitorResult_4490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 1, v___x_4499_);
                    v___x_4501_ = v_reuseFailAlloc_4502_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4501_;
            }
            5 => {
                v_toMonitorResult_4511_ = crate::leanh::lean_ctor_get(v___x_4488_, 0);
                v_isSharedCheck_4528_ = (!crate::leanh::lean_is_exclusive(v___x_4488_)) as u8;
                if v_isSharedCheck_4528_ == 0 {
                    v_unused_4529_ = crate::leanh::lean_ctor_get(v___x_4488_, 1);
                    crate::leanh::lean_dec(v_unused_4529_);
                    v___x_4513_ = v___x_4488_;
                    v_isShared_4514_ = v_isSharedCheck_4528_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toMonitorResult_4511_);
                    crate::leanh::lean_dec(v___x_4488_);
                    v___x_4513_ = crate::leanh::lean_box(0);
                    v_isShared_4514_ = v_isSharedCheck_4528_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_task_4515_ = crate::leanh::lean_ctor_get(v_a_4507_, 0);
                crate::leanh::lean_inc_ref(v_task_4515_);
                crate::leanh::lean_dec(v_a_4507_);
                v___x_4516_ = lean_io_wait(v_task_4515_);
                if crate::leanh::lean_obj_tag(v___x_4516_) == 0 {
                    v_a_4517_ = crate::leanh::lean_ctor_get(v___x_4516_, 0);
                    crate::leanh::lean_inc(v_a_4517_);
                    crate::leanh::lean_dec_ref_known(v___x_4516_, 2);
                    if v_isShared_4510_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4509_, 0, v_a_4517_);
                        v___x_4519_ = v___x_4509_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4523_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
                        v___x_4519_ = v_reuseFailAlloc_4523_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_4516_, 2);
                    crate::leanh::lean_del_object(v___x_4509_);
                    v___x_4524_ =
                        l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___closed__1;
                    if v_isShared_4514_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4513_, 1, v___x_4524_);
                        v___x_4526_ = v___x_4513_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_4527_,
                            0,
                            v_toMonitorResult_4511_,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4527_, 1, v___x_4524_);
                        v___x_4526_ = v_reuseFailAlloc_4527_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_4514_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4513_, 1, v___x_4519_);
                    v___x_4521_ = v___x_4513_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4522_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_toMonitorResult_4511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 1, v___x_4519_);
                    v___x_4521_ = v_reuseFailAlloc_4522_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4521_;
            }
            9 => {
                return v___x_4526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg___boxed(
    mut v_mctx_4531_: *mut crate::leanh::LeanObject,
    mut v_job_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4534_ =
        l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_4531_, v_job_4532_);
    crate::leanh::lean_dec_ref(v_mctx_4531_);
    return v_res_4534_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorBuild(
    mut v_00_u03b1_4535_: *mut crate::leanh::LeanObject,
    mut v_mctx_4536_: *mut crate::leanh::LeanObject,
    mut v_job_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4539_ =
        l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v_mctx_4536_, v_job_4537_);
    return v___x_4539_;
}
pub unsafe fn l___private_Lake_Build_Run_0__Lake_monitorBuild___boxed(
    mut v_00_u03b1_4540_: *mut crate::leanh::LeanObject,
    mut v_mctx_4541_: *mut crate::leanh::LeanObject,
    mut v_job_4542_: *mut crate::leanh::LeanObject,
    mut v_a_4543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4544_ = l___private_Lake_Build_Run_0__Lake_monitorBuild(
        v_00_u03b1_4540_,
        v_mctx_4541_,
        v_job_4542_,
    );
    crate::leanh::lean_dec_ref(v_mctx_4541_);
    return v_res_4544_;
}
pub unsafe fn l_Lake_Workspace_checkNoBuild___redArg(
    mut v_ws_4558_: *mut crate::leanh::LeanObject,
    mut v_build_4559_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: u8 = 0;
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4561_ = l_Lake_mkBuildContext___closed__0;
    v___x_4562_ = lean_st_mk_ref(v___x_4561_);
    v___x_4563_ = 0;
    v___x_4564_ = 1;
    v___x_4565_ = l_Lake_Workspace_checkNoBuild___redArg___closed__1;
    crate::leanh::lean_inc(v___x_4562_);
    v___x_4566_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v___x_4565_, v___x_4562_);
    v___x_4567_ =
        l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_4558_, v___x_4565_, v___x_4562_);
    v___x_4568_ = l_Lake_Workspace_checkNoBuild___redArg___closed__2;
    v___x_4569_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(
        v___x_4567_,
        v_build_4559_,
        v___x_4568_,
    );
    crate::leanh::lean_dec_ref(v___x_4567_);
    v___x_4570_ =
        l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_4566_, v___x_4569_);
    crate::leanh::lean_dec_ref(v___x_4566_);
    v_out_4571_ = crate::leanh::lean_ctor_get(v___x_4570_, 1);
    crate::leanh::lean_inc_ref(v_out_4571_);
    crate::leanh::lean_dec_ref(v___x_4570_);
    if crate::leanh::lean_obj_tag(v_out_4571_) == 0 {
        crate::leanh::lean_dec_ref_known(v_out_4571_, 1);
        return v___x_4563_;
    } else {
        crate::leanh::lean_dec_ref_known(v_out_4571_, 1);
        return v___x_4564_;
    }
}
pub unsafe fn l_Lake_Workspace_checkNoBuild___redArg___boxed(
    mut v_ws_4572_: *mut crate::leanh::LeanObject,
    mut v_build_4573_: *mut crate::leanh::LeanObject,
    mut v_a_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4575_: u8 = 0;
    let mut v_r_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4575_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_4572_, v_build_4573_);
    v_r_4576_ = crate::leanh::lean_box((v_res_4575_) as usize);
    return v_r_4576_;
}
pub unsafe fn l_Lake_Workspace_checkNoBuild(
    mut v_00_u03b1_4577_: *mut crate::leanh::LeanObject,
    mut v_ws_4578_: *mut crate::leanh::LeanObject,
    mut v_build_4579_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4581_: u8 = 0;
    v___x_4581_ = l_Lake_Workspace_checkNoBuild___redArg(v_ws_4578_, v_build_4579_);
    return v___x_4581_;
}
pub unsafe fn l_Lake_Workspace_checkNoBuild___boxed(
    mut v_00_u03b1_4582_: *mut crate::leanh::LeanObject,
    mut v_ws_4583_: *mut crate::leanh::LeanObject,
    mut v_build_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4586_: u8 = 0;
    let mut v_r_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4586_ = l_Lake_Workspace_checkNoBuild(v_00_u03b1_4582_, v_ws_4583_, v_build_4584_);
    v_r_4587_ = crate::leanh::lean_box((v_res_4586_) as usize);
    return v_r_4587_;
}
pub unsafe fn l_Lake_Workspace_runBuild___redArg(
    mut v_ws_4588_: *mut crate::leanh::LeanObject,
    mut v_build_4589_: *mut crate::leanh::LeanObject,
    mut v_cfg_4590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4592_ = l_Lake_mkBuildContext___closed__0;
    v___x_4593_ = lean_st_mk_ref(v___x_4592_);
    crate::leanh::lean_inc(v___x_4593_);
    v___x_4594_ = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(v_cfg_4590_, v___x_4593_);
    crate::leanh::lean_inc_ref(v_cfg_4590_);
    v___x_4595_ =
        l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(v_ws_4588_, v_cfg_4590_, v___x_4593_);
    v___x_4596_ = l_Lake_Workspace_checkNoBuild___redArg___closed__2;
    v___x_4597_ = l___private_Lake_Build_Run_0__Lake_Workspace_startBuild___redArg(
        v___x_4595_,
        v_build_4589_,
        v___x_4596_,
    );
    v___x_4598_ =
        l___private_Lake_Build_Run_0__Lake_monitorBuild___redArg(v___x_4594_, v___x_4597_);
    v___x_4599_ = l___private_Lake_Build_Run_0__Lake_finalizeBuild___redArg(
        v_cfg_4590_,
        v___x_4595_,
        v___x_4594_,
        v___x_4598_,
    );
    crate::leanh::lean_dec_ref(v___x_4595_);
    return v___x_4599_;
}
pub unsafe fn l_Lake_Workspace_runBuild___redArg___boxed(
    mut v_ws_4600_: *mut crate::leanh::LeanObject,
    mut v_build_4601_: *mut crate::leanh::LeanObject,
    mut v_cfg_4602_: *mut crate::leanh::LeanObject,
    mut v_a_4603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4604_ = l_Lake_Workspace_runBuild___redArg(v_ws_4600_, v_build_4601_, v_cfg_4602_);
    return v_res_4604_;
}
pub unsafe fn l_Lake_Workspace_runBuild(
    mut v_00_u03b1_4605_: *mut crate::leanh::LeanObject,
    mut v_ws_4606_: *mut crate::leanh::LeanObject,
    mut v_build_4607_: *mut crate::leanh::LeanObject,
    mut v_cfg_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4610_ = l_Lake_Workspace_runBuild___redArg(v_ws_4606_, v_build_4607_, v_cfg_4608_);
    return v___x_4610_;
}
pub unsafe fn l_Lake_Workspace_runBuild___boxed(
    mut v_00_u03b1_4611_: *mut crate::leanh::LeanObject,
    mut v_ws_4612_: *mut crate::leanh::LeanObject,
    mut v_build_4613_: *mut crate::leanh::LeanObject,
    mut v_cfg_4614_: *mut crate::leanh::LeanObject,
    mut v_a_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4616_ =
        l_Lake_Workspace_runBuild(v_00_u03b1_4611_, v_ws_4612_, v_build_4613_, v_cfg_4614_);
    return v_res_4616_;
}
pub unsafe fn l_Lake_runBuild___redArg(
    mut v_build_4617_: *mut crate::leanh::LeanObject,
    mut v_cfg_4618_: *mut crate::leanh::LeanObject,
    mut v_a_4619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_4619_);
    v___x_4621_ = l_Lake_Workspace_runBuild___redArg(v_a_4619_, v_build_4617_, v_cfg_4618_);
    return v___x_4621_;
}
pub unsafe fn l_Lake_runBuild___redArg___boxed(
    mut v_build_4622_: *mut crate::leanh::LeanObject,
    mut v_cfg_4623_: *mut crate::leanh::LeanObject,
    mut v_a_4624_: *mut crate::leanh::LeanObject,
    mut v_a_4625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4626_ = l_Lake_runBuild___redArg(v_build_4622_, v_cfg_4623_, v_a_4624_);
    crate::leanh::lean_dec(v_a_4624_);
    return v_res_4626_;
}
pub unsafe fn l_Lake_runBuild(
    mut v_00_u03b1_4627_: *mut crate::leanh::LeanObject,
    mut v_build_4628_: *mut crate::leanh::LeanObject,
    mut v_cfg_4629_: *mut crate::leanh::LeanObject,
    mut v_a_4630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_4630_);
    v___x_4632_ = l_Lake_Workspace_runBuild___redArg(v_a_4630_, v_build_4628_, v_cfg_4629_);
    return v___x_4632_;
}
pub unsafe fn l_Lake_runBuild___boxed(
    mut v_00_u03b1_4633_: *mut crate::leanh::LeanObject,
    mut v_build_4634_: *mut crate::leanh::LeanObject,
    mut v_cfg_4635_: *mut crate::leanh::LeanObject,
    mut v_a_4636_: *mut crate::leanh::LeanObject,
    mut v_a_4637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4638_ = l_Lake_runBuild(v_00_u03b1_4633_, v_build_4634_, v_cfg_4635_, v_a_4636_);
    crate::leanh::lean_dec(v_a_4636_);
    return v_res_4638_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Run(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Index(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__1,
    );
    l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2();
    crate::leanh::lean_mark_persistent(
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__2,
    );
    l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3();
    crate::leanh::lean_mark_persistent(
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__3,
    );
    l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4();
    crate::leanh::lean_mark_persistent(
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__4,
    );
    l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5();
    crate::leanh::lean_mark_persistent(
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__5,
    );
    l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6();
    crate::leanh::lean_mark_persistent(
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__6,
    );
    l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7();
    crate::leanh::lean_mark_persistent(
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__7,
    );
    l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8 = _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8();
    crate::leanh::lean_mark_persistent(
        l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames___closed__0___boxed__const__8,
    );
    l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames =
        _init_l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames();
    crate::leanh::lean_mark_persistent(l___private_Lake_Build_Run_0__Lake_Monitor_spinnerFrames);
    l_Lake_noBuildCode = _init_l_Lake_noBuildCode();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Run(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Run(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Index(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Run(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Run(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Run(builtin);
}

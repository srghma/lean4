// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: Lake.Load.Config Lake.Build.Context Lake.Util.Exit Lake.Build.Run Lake.Build.Module Lake.Load.Package Lake.Load.Lean.Elab Lake.Load.Workspace Lake.Util.IO
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_get_stderr, lean_get_stdout, lean_io_getenv, lean_io_process_child_wait,
    lean_io_process_spawn, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_panic_fn_borrowed, lean_string_append, lean_string_dec_eq,
    lean_string_push, lean_string_utf8_byte_size, lean_usize_add, lean_usize_dec_eq,
    lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::l_instInhabitedOfMonad___redArg;
use crate::r#gen::Init::System::IO::l_instMonadBaseIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Build::Context::{
    initialize_Lake_Build_Context, runtime_initialize_Lake_Build_Context,
};
use crate::r#gen::Lake::Build::Module::{
    initialize_Lake_Build_Module, l_Lake_setupServerModule___boxed,
    runtime_initialize_Lake_Build_Module,
};
use crate::r#gen::Lake::Build::Run::{
    initialize_Lake_Build_Run, l_Lake_Workspace_runBuild___redArg,
    runtime_initialize_Lake_Build_Run,
};
use crate::r#gen::Lake::Config::Env::l_Lake_Env_baseVars;
use crate::r#gen::Lake::Config::Workspace::l_Lake_Workspace_augmentedEnvVars;
use crate::r#gen::Lake::Load::Config::{
    initialize_Lake_Load_Config, runtime_initialize_Lake_Load_Config,
};
use crate::r#gen::Lake::Load::Lean::Elab::{
    initialize_Lake_Load_Lean_Elab, l_Lake_configModuleName, runtime_initialize_Lake_Load_Lean_Elab,
};
use crate::r#gen::Lake::Load::Package::{
    initialize_Lake_Load_Package, l_Lake_realConfigFile, runtime_initialize_Lake_Load_Package,
};
use crate::r#gen::Lake::Load::Workspace::{
    initialize_Lake_Load_Workspace, l_Lake_loadWorkspace, l_Lake_loadWorkspace___boxed,
    runtime_initialize_Lake_Load_Workspace,
};
use crate::r#gen::Lake::Util::Exit::{
    initialize_Lake_Util_Exit, runtime_initialize_Lake_Util_Exit,
};
use crate::r#gen::Lake::Util::IO::{
    initialize_Lake_Util_IO, l_Lake_resolvePath, runtime_initialize_Lake_Util_IO,
};
use crate::r#gen::Lake::Util::Log::{
    l_Lake_AnsiMode_isEnabled, l_Lake_Log_toString, l_Lake_LoggerIO_captureLog___redArg,
    l_Lake_OutStream_get, l_Lake_OutStream_logEntry, l_Lake_logToStream,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::Setup::{l_Lean_Plugin_ofFilePath, l_Lean_instToJsonModuleSetup_toJson};
pub static mut l_Lake_noConfigFileCode: u32 = 0;
pub static l_Lake_invalidConfigEnvVar___closed__0_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
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
            76, 65, 75, 69, 95, 73, 78, 86, 65, 76, 73, 68, 95, 67, 79, 78, 70, 73, 71, 0,
        ],
    };
static mut l_Lake_invalidConfigEnvVar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_invalidConfigEnvVar___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_invalidConfigEnvVar: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_invalidConfigEnvVar___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0_value:
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
        76, 97, 107, 101, 46, 67, 76, 73, 46, 83, 101, 114, 118, 101, 0,
    ],
};
static mut l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1_value:
    crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 97, 107, 101, 46, 67, 76, 73, 46, 83, 101,
        114, 118, 101, 46, 48, 46, 76, 97, 107, 101, 46, 115, 101, 116, 117, 112, 70, 105, 108,
        101, 46, 112, 114, 105, 110, 116, 33, 0,
    ],
};
static mut l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2_value:
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
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 114, 105, 110, 116, 32, 96, 115, 101,
        116, 117, 112, 45, 102, 105, 108, 101, 96, 32, 114, 101, 115, 117, 108, 116, 58, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 97, 107, 101, 46, 67, 76, 73, 46, 83, 101,
        114, 118, 101, 46, 48, 46, 76, 97, 107, 101, 46, 115, 101, 116, 117, 112, 70, 105, 108,
        101, 46, 101, 112, 114, 105, 110, 116, 33, 0,
    ],
};
static mut l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 114, 105, 110, 116, 32, 96, 115, 101,
        116, 117, 112, 45, 102, 105, 108, 101, 96, 32, 101, 114, 114, 111, 114, 58, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        10, 79, 114, 105, 103, 105, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_setupFile___closed__0_value: crate::leanh::LeanStringObject<97> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 97,
        m_capacity: 97,
        m_length: 96,
        m_data: [
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111, 110, 102, 105, 103, 117, 114,
            101, 32, 116, 104, 101, 32, 76, 97, 107, 101, 32, 119, 111, 114, 107, 115, 112, 97, 99,
            101, 46, 32, 80, 108, 101, 97, 115, 101, 32, 114, 101, 115, 116, 97, 114, 116, 32, 116,
            104, 101, 32, 115, 101, 114, 118, 101, 114, 32, 97, 102, 116, 101, 114, 32, 102, 105,
            120, 105, 110, 103, 32, 116, 104, 101, 32, 101, 114, 114, 111, 114, 32, 97, 98, 111,
            118, 101, 46, 10, 0,
        ],
    };
static mut l_Lake_setupFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_setupFile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_setupFile___closed__1_value: crate::leanh::LeanStringObject<38> =
    crate::leanh::LeanStringObject {
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
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 98, 117, 105, 108, 100, 32, 109, 111,
            100, 117, 108, 101, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 105, 101, 115, 46,
            10, 0,
        ],
    };
static mut l_Lake_setupFile___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_setupFile___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_setupFile___closed__2_value: crate::leanh::LeanStringObject<36> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 108, 111, 97, 100, 32, 116, 104, 101, 32,
            76, 97, 107, 101, 32, 119, 111, 114, 107, 115, 112, 97, 99, 101, 46, 10, 0,
        ],
    };
static mut l_Lake_setupFile___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_setupFile___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_setupFile___closed__3_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_setupFile___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_setupFile___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_serve___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [65793 as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_serve___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_serve___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_serve___closed__1_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [45, 45, 115, 101, 114, 118, 101, 114, 0],
    };
static mut l_Lake_serve___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_serve___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_serve___closed__2_value: crate::leanh::LeanArrayObject<1> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [
            core::ptr::addr_of!(l_Lake_serve___closed__1_value) as *mut crate::leanh::LeanObject
        ],
    };
static mut l_Lake_serve___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_serve___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_serve___closed__3_value: crate::leanh::LeanStringObject<81> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 81,
        m_capacity: 81,
        m_length: 80,
        m_data: [
            119, 97, 114, 110, 105, 110, 103, 58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 99, 111,
            110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 104, 97, 115, 32, 101, 114,
            114, 111, 114, 115, 44, 32, 102, 97, 108, 108, 105, 110, 103, 32, 98, 97, 99, 107, 32,
            116, 111, 32, 112, 108, 97, 105, 110, 32, 96, 108, 101, 97, 110, 32, 45, 45, 115, 101,
            114, 118, 101, 114, 96, 0,
        ],
    };
static mut l_Lake_serve___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_serve___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake_noConfigFileCode() -> u32 {
    let mut v___x_297_: u32 = 0;
    v___x_297_ = 2;
    return v___x_297_;
}
pub unsafe fn _init_l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = crate::leanh::lean_box(0);
    v___x_301_ = l_instMonadBaseIO;
    v___x_302_ = l_instInhabitedOfMonad___redArg(v___x_301_, v___x_300_);
    return v___x_302_;
}
pub unsafe fn l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(
    mut v_msg_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284__overap_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0_once), _init_l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0);
    v___x_284__overap_306_ = lean_panic_fn_borrowed(v___x_305_, v_msg_303_);
    v___x_307_ = crate::leanh::lean_apply_1(v___x_284__overap_306_, crate::leanh::lean_box(0));
    return v___x_307_;
}
pub unsafe fn l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___boxed(
    mut v_msg_308_: *mut crate::leanh::LeanObject,
    mut v___y_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_310_ =
        l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(v_msg_308_);
    return v_res_310_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(
    mut v_s_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_313_ = lean_get_stdout();
    v_putStr_314_ = crate::leanh::lean_ctor_get(v___x_313_, 4);
    crate::leanh::lean_inc_ref(v_putStr_314_);
    crate::leanh::lean_dec_ref(v___x_313_);
    v___x_315_ = crate::leanh::lean_apply_2(v_putStr_314_, v_s_311_, crate::leanh::lean_box(0));
    return v___x_315_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0___boxed(
    mut v_s_316_: *mut crate::leanh::LeanObject,
    mut v_a_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(v_s_316_);
    return v_res_318_;
}
pub unsafe fn l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(
    mut v_s_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_321_: u32 = 0;
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_321_ = 10;
    v___x_322_ = lean_string_push(v_s_319_, v___x_321_);
    v___x_323_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(v___x_322_);
    return v___x_323_;
}
pub unsafe fn l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0___boxed(
    mut v_s_324_: *mut crate::leanh::LeanObject,
    mut v_a_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(
        v_s_324_,
    );
    return v_res_326_;
}
pub unsafe fn l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(
    mut v_msg_330_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(
        v_msg_330_,
    );
    if crate::leanh::lean_obj_tag(v___x_332_) == 0 {
        let mut v___x_333_: u32 = 0;
        crate::leanh::lean_dec_ref_known(v___x_332_, 1);
        v___x_333_ = 0;
        return v___x_333_;
    } else {
        let mut v_a_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_344_: u32 = 0;
        v_a_334_ = crate::leanh::lean_ctor_get(v___x_332_, 0);
        crate::leanh::lean_inc(v_a_334_);
        crate::leanh::lean_dec_ref_known(v___x_332_, 1);
        v___x_335_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0;
        v___x_336_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1;
        v___x_337_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_338_ = crate::leanh::lean_unsigned_to_nat(6);
        v___x_339_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2;
        v___x_340_ = lean_io_error_to_string(v_a_334_);
        v___x_341_ = lean_string_append(v___x_339_, v___x_340_);
        crate::leanh::lean_dec_ref(v___x_340_);
        v___x_342_ =
            l_mkPanicMessageWithDecl(v___x_335_, v___x_336_, v___x_337_, v___x_338_, v___x_341_);
        crate::leanh::lean_dec_ref(v___x_341_);
        v___x_343_ = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(
            v___x_342_,
        );
        v___x_344_ = 1;
        return v___x_344_;
    }
}
pub unsafe fn l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed(
    mut v_msg_345_: *mut crate::leanh::LeanObject,
    mut v_a_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_347_: u32 = 0;
    let mut v_r_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_347_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v_msg_345_);
    v_r_348_ = crate::leanh::lean_box_uint32(v_res_347_);
    return v_r_348_;
}
pub unsafe fn l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(
    mut v_s_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = lean_get_stderr();
    v_putStr_352_ = crate::leanh::lean_ctor_get(v___x_351_, 4);
    crate::leanh::lean_inc_ref(v_putStr_352_);
    crate::leanh::lean_dec_ref(v___x_351_);
    v___x_353_ = crate::leanh::lean_apply_2(v_putStr_352_, v_s_349_, crate::leanh::lean_box(0));
    return v___x_353_;
}
pub unsafe fn l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0___boxed(
    mut v_s_354_: *mut crate::leanh::LeanObject,
    mut v_a_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_356_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(
        v_s_354_,
    );
    return v_res_356_;
}
pub unsafe fn l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(
    mut v_msg_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_msg_360_);
    v___x_362_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(
        v_msg_360_,
    );
    if crate::leanh::lean_obj_tag(v___x_362_) == 0 {
        let mut v_a_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_msg_360_);
        v_a_363_ = crate::leanh::lean_ctor_get(v___x_362_, 0);
        crate::leanh::lean_inc(v_a_363_);
        crate::leanh::lean_dec_ref_known(v___x_362_, 1);
        return v_a_363_;
    } else {
        let mut v_a_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_364_ = crate::leanh::lean_ctor_get(v___x_362_, 0);
        crate::leanh::lean_inc(v_a_364_);
        crate::leanh::lean_dec_ref_known(v___x_362_, 1);
        v___x_365_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0;
        v___x_366_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0;
        v___x_367_ = crate::leanh::lean_unsigned_to_nat(84);
        v___x_368_ = crate::leanh::lean_unsigned_to_nat(6);
        v___x_369_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1;
        v___x_370_ = lean_io_error_to_string(v_a_364_);
        v___x_371_ = lean_string_append(v___x_369_, v___x_370_);
        crate::leanh::lean_dec_ref(v___x_370_);
        v___x_372_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2;
        v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
        v___x_374_ = lean_string_append(v___x_373_, v_msg_360_);
        crate::leanh::lean_dec_ref(v_msg_360_);
        v___x_375_ =
            l_mkPanicMessageWithDecl(v___x_365_, v___x_366_, v___x_367_, v___x_368_, v___x_374_);
        crate::leanh::lean_dec_ref(v___x_374_);
        v___x_376_ = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(
            v___x_375_,
        );
        return v___x_376_;
    }
}
pub unsafe fn l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___boxed(
    mut v_msg_377_: *mut crate::leanh::LeanObject,
    mut v_a_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_379_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v_msg_377_);
    return v_res_379_;
}
pub unsafe fn l_Lake_setupFile___lam__0(
    mut v_val_380_: *mut crate::leanh::LeanObject,
    mut v_outLv_381_: u8,
    mut v_val_382_: u8,
    mut v_e_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = l_Lake_logToStream(v_e_383_, v_val_380_, v_outLv_381_, v_val_382_);
    return v___x_385_;
}
pub unsafe fn l_Lake_setupFile___lam__0___boxed(
    mut v_val_386_: *mut crate::leanh::LeanObject,
    mut v_outLv_387_: *mut crate::leanh::LeanObject,
    mut v_val_388_: *mut crate::leanh::LeanObject,
    mut v_e_389_: *mut crate::leanh::LeanObject,
    mut v___y_390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_outLv_boxed_391_: u8 = 0;
    let mut v_val_1515__boxed_392_: u8 = 0;
    let mut v_res_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_outLv_boxed_391_ = (crate::leanh::lean_unbox(v_outLv_387_) as u8);
    v_val_1515__boxed_392_ = (crate::leanh::lean_unbox(v_val_388_) as u8);
    v_res_393_ = l_Lake_setupFile___lam__0(
        v_val_386_,
        v_outLv_boxed_391_,
        v_val_1515__boxed_392_,
        v_e_389_,
    );
    crate::leanh::lean_dec_ref(v_e_389_);
    return v_res_393_;
}
pub unsafe fn l_Lake_setupFile(
    mut v_loadConfig_399_: *mut crate::leanh::LeanObject,
    mut v_leanFile_400_: *mut crate::leanh::LeanObject,
    mut v_header_x3f_401_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_402_: *mut crate::leanh::LeanObject,
) -> u32 {
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: u8 = 0;
    crate::leanh::lean_inc_ref(v_leanFile_400_);
    v___x_404_ = l_Lake_resolvePath(v_leanFile_400_);
    v_lakeEnv_405_ = crate::leanh::lean_ctor_get(v_loadConfig_399_, 0);
    v_configFile_406_ = crate::leanh::lean_ctor_get(v_loadConfig_399_, 8);
    crate::leanh::lean_inc_ref(v_configFile_406_);
    v___x_407_ = l_Lake_realConfigFile(v_configFile_406_);
    v___x_408_ = lean_string_utf8_byte_size(v___x_407_);
    v___x_409_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_410_ = lean_nat_dec_eq(v___x_408_, v___x_409_);
    if v___x_410_ == 0 {
        let mut v___x_411_: u8 = 0;
        v___x_411_ = lean_string_dec_eq(v___x_407_, v___x_404_);
        crate::leanh::lean_dec_ref(v___x_407_);
        if v___x_411_ == 0 {
            let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_412_ = l_Lake_invalidConfigEnvVar___closed__0;
            v___x_413_ = lean_io_getenv(v___x_412_);
            if crate::leanh::lean_obj_tag(v___x_413_) == 1 {
                let mut v_val_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_418_: u32 = 0;
                crate::leanh::lean_dec_ref(v___x_404_);
                crate::leanh::lean_dec_ref(v_buildConfig_402_);
                crate::leanh::lean_dec(v_header_x3f_401_);
                crate::leanh::lean_dec_ref(v_leanFile_400_);
                crate::leanh::lean_dec_ref(v_loadConfig_399_);
                v_val_414_ = crate::leanh::lean_ctor_get(v___x_413_, 0);
                crate::leanh::lean_inc(v_val_414_);
                crate::leanh::lean_dec_ref_known(v___x_413_, 1);
                v___x_415_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v_val_414_);
                v___x_416_ = l_Lake_setupFile___closed__0;
                v___x_417_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v___x_416_);
                v___x_418_ = 1;
                return v___x_418_;
            } else {
                let mut v_toLogConfig_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_outLv_420_: u8 = 0;
                let mut v_ansiMode_421_: u8 = 0;
                let mut v_out_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_424_: u8 = 0;
                let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_413_);
                v_toLogConfig_419_ = crate::leanh::lean_ctor_get(v_buildConfig_402_, 0);
                v_outLv_420_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLogConfig_419_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_421_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLogConfig_419_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_422_ = crate::leanh::lean_ctor_get(v_toLogConfig_419_, 0);
                v___x_423_ = l_Lake_OutStream_get(v_out_422_);
                crate::leanh::lean_inc_ref(v___x_423_);
                v___x_424_ = l_Lake_AnsiMode_isEnabled(v___x_423_, v_ansiMode_421_);
                v___x_425_ = crate::leanh::lean_box((v_outLv_420_) as usize);
                v___x_426_ = crate::leanh::lean_box((v___x_424_) as usize);
                v___f_427_ = crate::leanh::lean_alloc_closure(
                    l_Lake_setupFile___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_427_, 0, v___x_423_);
                crate::leanh::lean_closure_set(v___f_427_, 1, v___x_425_);
                crate::leanh::lean_closure_set(v___f_427_, 2, v___x_426_);
                v___x_428_ = l_Lake_loadWorkspace(v_loadConfig_399_, v___f_427_);
                crate::leanh::lean_dec_ref(v___f_427_);
                if crate::leanh::lean_obj_tag(v___x_428_) == 0 {
                    let mut v_a_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_a_429_ = crate::leanh::lean_ctor_get(v___x_428_, 0);
                    crate::leanh::lean_inc(v_a_429_);
                    crate::leanh::lean_dec_ref_known(v___x_428_, 1);
                    v___x_430_ = crate::leanh::lean_alloc_closure(
                        l_Lake_setupServerModule___boxed as *mut core::ffi::c_void,
                        10,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_430_, 0, v_leanFile_400_);
                    crate::leanh::lean_closure_set(v___x_430_, 1, v___x_404_);
                    crate::leanh::lean_closure_set(v___x_430_, 2, v_header_x3f_401_);
                    v___x_431_ = l_Lake_Workspace_runBuild___redArg(
                        v_a_429_,
                        v___x_430_,
                        v_buildConfig_402_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_431_) == 0 {
                        let mut v_a_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_435_: u32 = 0;
                        v_a_432_ = crate::leanh::lean_ctor_get(v___x_431_, 0);
                        crate::leanh::lean_inc(v_a_432_);
                        crate::leanh::lean_dec_ref_known(v___x_431_, 1);
                        v___x_433_ = l_Lean_instToJsonModuleSetup_toJson(v_a_432_);
                        v___x_434_ = l_Lean_Json_compress(v___x_433_);
                        v___x_435_ =
                            l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v___x_434_);
                        return v___x_435_;
                    } else {
                        let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_438_: u32 = 0;
                        crate::leanh::lean_dec_ref_known(v___x_431_, 1);
                        v___x_436_ = l_Lake_setupFile___closed__1;
                        v___x_437_ =
                            l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v___x_436_);
                        v___x_438_ = 1;
                        return v___x_438_;
                    }
                } else {
                    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_441_: u32 = 0;
                    crate::leanh::lean_dec_ref_known(v___x_428_, 1);
                    crate::leanh::lean_dec_ref(v___x_404_);
                    crate::leanh::lean_dec_ref(v_buildConfig_402_);
                    crate::leanh::lean_dec(v_header_x3f_401_);
                    crate::leanh::lean_dec_ref(v_leanFile_400_);
                    v___x_439_ = l_Lake_setupFile___closed__2;
                    v___x_440_ =
                        l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(v___x_439_);
                    v___x_441_ = 1;
                    return v___x_441_;
                }
            }
        } else {
            let mut v_lake_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_sharedDynlib_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_path_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_456_: u32 = 0;
            crate::leanh::lean_inc_ref(v_lakeEnv_405_);
            crate::leanh::lean_dec_ref(v___x_404_);
            crate::leanh::lean_dec_ref(v_buildConfig_402_);
            crate::leanh::lean_dec(v_header_x3f_401_);
            crate::leanh::lean_dec_ref(v_leanFile_400_);
            crate::leanh::lean_dec_ref(v_loadConfig_399_);
            v_lake_442_ = crate::leanh::lean_ctor_get(v_lakeEnv_405_, 0);
            crate::leanh::lean_inc_ref(v_lake_442_);
            crate::leanh::lean_dec_ref(v_lakeEnv_405_);
            v_sharedDynlib_443_ = crate::leanh::lean_ctor_get(v_lake_442_, 4);
            crate::leanh::lean_inc_ref(v_sharedDynlib_443_);
            crate::leanh::lean_dec_ref(v_lake_442_);
            v_path_444_ = crate::leanh::lean_ctor_get(v_sharedDynlib_443_, 0);
            crate::leanh::lean_inc_ref(v_path_444_);
            crate::leanh::lean_dec_ref(v_sharedDynlib_443_);
            v___x_445_ = l_Lake_configModuleName;
            v___x_446_ = crate::leanh::lean_box(0);
            v___x_447_ = crate::leanh::lean_box(1);
            v___x_448_ = l_Lake_setupFile___closed__3;
            v___x_449_ = l_Lean_Plugin_ofFilePath(v_path_444_);
            v___x_450_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
            v___x_452_ = lean_array_push(v___x_451_, v___x_449_);
            v___x_453_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_453_, 0, v___x_445_);
            crate::leanh::lean_ctor_set(v___x_453_, 1, v___x_446_);
            crate::leanh::lean_ctor_set(v___x_453_, 2, v___x_446_);
            crate::leanh::lean_ctor_set(v___x_453_, 3, v___x_447_);
            crate::leanh::lean_ctor_set(v___x_453_, 4, v___x_448_);
            crate::leanh::lean_ctor_set(v___x_453_, 5, v___x_452_);
            crate::leanh::lean_ctor_set(v___x_453_, 6, v___x_447_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_453_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                v___x_410_,
            );
            v___x_454_ = l_Lean_instToJsonModuleSetup_toJson(v___x_453_);
            v___x_455_ = l_Lean_Json_compress(v___x_454_);
            v___x_456_ = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(v___x_455_);
            return v___x_456_;
        }
    } else {
        let mut v___x_457_: u32 = 0;
        crate::leanh::lean_dec_ref(v___x_407_);
        crate::leanh::lean_dec_ref(v___x_404_);
        crate::leanh::lean_dec_ref(v_buildConfig_402_);
        crate::leanh::lean_dec(v_header_x3f_401_);
        crate::leanh::lean_dec_ref(v_leanFile_400_);
        crate::leanh::lean_dec_ref(v_loadConfig_399_);
        v___x_457_ = 2;
        return v___x_457_;
    }
}
pub unsafe fn l_Lake_setupFile___boxed(
    mut v_loadConfig_458_: *mut crate::leanh::LeanObject,
    mut v_leanFile_459_: *mut crate::leanh::LeanObject,
    mut v_header_x3f_460_: *mut crate::leanh::LeanObject,
    mut v_buildConfig_461_: *mut crate::leanh::LeanObject,
    mut v_a_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_463_: u32 = 0;
    let mut v_r_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_463_ = l_Lake_setupFile(
        v_loadConfig_458_,
        v_leanFile_459_,
        v_header_x3f_460_,
        v_buildConfig_461_,
    );
    v_r_464_ = crate::leanh::lean_box_uint32(v_res_463_);
    return v_r_464_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(
    mut v_as_465_: *mut crate::leanh::LeanObject,
    mut v_i_466_: usize,
    mut v_stop_467_: usize,
    mut v_b_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_470_: u8 = 0;
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: u8 = 0;
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: usize = 0;
    let mut v___x_477_: usize = 0;
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_470_ = lean_usize_dec_eq(v_i_466_, v_stop_467_);
                if v___x_470_ == 0 {
                    v___x_471_ = crate::leanh::lean_box(1);
                    v___x_472_ = 1;
                    v___x_473_ = 0;
                    v___x_474_ = lean_array_uget_borrowed(v_as_465_, v_i_466_);
                    v___x_475_ =
                        l_Lake_OutStream_logEntry(v___x_471_, v___x_474_, v___x_472_, v___x_473_);
                    v___x_476_ = 1usize;
                    v___x_477_ = lean_usize_add(v_i_466_, v___x_476_);
                    v_i_466_ = v___x_477_;
                    v_b_468_ = v___x_475_;
                    state = 0;
                    continue;
                } else {
                    v___x_479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_479_, 0, v_b_468_);
                    return v___x_479_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1___boxed(
    mut v_as_480_: *mut crate::leanh::LeanObject,
    mut v_i_481_: *mut crate::leanh::LeanObject,
    mut v_stop_482_: *mut crate::leanh::LeanObject,
    mut v_b_483_: *mut crate::leanh::LeanObject,
    mut v___y_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_485_: usize = 0;
    let mut v_stop_boxed_486_: usize = 0;
    let mut v_res_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_485_ = crate::leanh::lean_unbox_usize(v_i_481_);
    crate::leanh::lean_dec(v_i_481_);
    v_stop_boxed_486_ = crate::leanh::lean_unbox_usize(v_stop_482_);
    crate::leanh::lean_dec(v_stop_482_);
    v_res_487_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(
            v_as_480_,
            v_i_boxed_485_,
            v_stop_boxed_486_,
            v_b_483_,
        );
    crate::leanh::lean_dec_ref(v_as_480_);
    return v_res_487_;
}
pub unsafe fn l_IO_eprintln___at___00Lake_serve_spec__0(
    mut v_s_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_490_: u32 = 0;
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = 10;
    v___x_491_ = lean_string_push(v_s_488_, v___x_490_);
    v___x_492_ = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(
        v___x_491_,
    );
    return v___x_492_;
}
pub unsafe fn l_IO_eprintln___at___00Lake_serve_spec__0___boxed(
    mut v_s_493_: *mut crate::leanh::LeanObject,
    mut v_a_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_495_ = l_IO_eprintln___at___00Lake_serve_spec__0(v_s_493_);
    return v_res_495_;
}
pub unsafe fn l_Lake_serve(
    mut v_config_504_: *mut crate::leanh::LeanObject,
    mut v_args_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u8 = 0;
    let mut v___x_519_: u8 = 0;
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_527_: u8 = 0;
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_531_: u8 = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_538_: u8 = 0;
    let mut v_val_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreGlobalServerArgs_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeEnv_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_562_: u8 = 0;
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_566_: u8 = 0;
    let mut v___y_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_576_: u8 = 0;
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: usize = 0;
    let mut v___x_583_: usize = 0;
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: usize = 0;
    let mut v___x_586_: usize = 0;
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_config_504_);
                v___x_532_ = crate::leanh::lean_alloc_closure(
                    l_Lake_loadWorkspace___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_532_, 0, v_config_504_);
                v___x_533_ = l_Lake_LoggerIO_captureLog___redArg(v___x_532_);
                v_fst_534_ = crate::leanh::lean_ctor_get(v___x_533_, 0);
                v_snd_535_ = crate::leanh::lean_ctor_get(v___x_533_, 1);
                v_isSharedCheck_588_ = (!crate::leanh::lean_is_exclusive(v___x_533_)) as u8;
                if v_isSharedCheck_588_ == 0 {
                    v___x_537_ = v___x_533_;
                    v_isShared_538_ = v_isSharedCheck_588_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_535_);
                    crate::leanh::lean_inc(v_fst_534_);
                    crate::leanh::lean_dec(v___x_533_);
                    v___x_537_ = crate::leanh::lean_box(0);
                    v_isShared_538_ = v_isSharedCheck_588_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_510_ = l_Lake_serve___closed__0;
                v_lakeEnv_511_ = crate::leanh::lean_ctor_get(v_config_504_, 0);
                crate::leanh::lean_inc_ref(v_lakeEnv_511_);
                crate::leanh::lean_dec_ref(v_config_504_);
                v_lean_512_ = crate::leanh::lean_ctor_get(v_lakeEnv_511_, 1);
                crate::leanh::lean_inc_ref(v_lean_512_);
                crate::leanh::lean_dec_ref(v_lakeEnv_511_);
                v_lean_513_ = crate::leanh::lean_ctor_get(v_lean_512_, 7);
                crate::leanh::lean_inc_ref(v_lean_513_);
                crate::leanh::lean_dec_ref(v_lean_512_);
                v___x_514_ = l_Lake_serve___closed__2;
                v___x_515_ = l_Array_append___redArg(v___x_514_, v_snd_509_);
                crate::leanh::lean_dec_ref(v_snd_509_);
                v___x_516_ = l_Array_append___redArg(v___x_515_, v_args_505_);
                v___x_517_ = crate::leanh::lean_box(0);
                v___x_518_ = 1;
                v___x_519_ = 0;
                v___x_520_ = crate::leanh::lean_alloc_ctor(0, 5, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_520_, 0, v___x_510_);
                crate::leanh::lean_ctor_set(v___x_520_, 1, v_lean_513_);
                crate::leanh::lean_ctor_set(v___x_520_, 2, v___x_516_);
                crate::leanh::lean_ctor_set(v___x_520_, 3, v___x_517_);
                crate::leanh::lean_ctor_set(v___x_520_, 4, v_fst_508_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_520_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_518_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_520_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_519_,
                );
                v___x_521_ = lean_io_process_spawn(v___x_520_);
                if crate::leanh::lean_obj_tag(v___x_521_) == 0 {
                    v_a_522_ = crate::leanh::lean_ctor_get(v___x_521_, 0);
                    crate::leanh::lean_inc(v_a_522_);
                    crate::leanh::lean_dec_ref_known(v___x_521_, 1);
                    v___x_523_ = lean_io_process_child_wait(v___x_510_, v_a_522_);
                    crate::leanh::lean_dec(v_a_522_);
                    return v___x_523_;
                } else {
                    v_a_524_ = crate::leanh::lean_ctor_get(v___x_521_, 0);
                    v_isSharedCheck_531_ = (!crate::leanh::lean_is_exclusive(v___x_521_)) as u8;
                    if v_isSharedCheck_531_ == 0 {
                        v___x_526_ = v___x_521_;
                        v_isShared_527_ = v_isSharedCheck_531_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_524_);
                        crate::leanh::lean_dec(v___x_521_);
                        v___x_526_ = crate::leanh::lean_box(0);
                        v_isShared_527_ = v_isSharedCheck_531_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_527_ == 0 {
                    v___x_529_ = v___x_526_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
                    v___x_529_ = v_reuseFailAlloc_530_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_529_;
            }
            4 => {
                v___x_577_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_578_ = lean_array_get_size(v_snd_535_);
                v___x_579_ = lean_nat_dec_lt(v___x_577_, v___x_578_);
                if v___x_579_ == 0 {
                    state = 5;
                    continue;
                } else {
                    v___x_580_ = crate::leanh::lean_box(0);
                    v___x_581_ = lean_nat_dec_le(v___x_578_, v___x_578_);
                    if v___x_581_ == 0 {
                        if v___x_579_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            v___x_582_ = 0usize;
                            v___x_583_ = lean_usize_of_nat(v___x_578_);
                            v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(v_snd_535_, v___x_582_, v___x_583_, v___x_580_);
                            v___y_568_ = v___x_584_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___x_585_ = 0usize;
                        v___x_586_ = lean_usize_of_nat(v___x_578_);
                        v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(v_snd_535_, v___x_585_, v___x_586_, v___x_580_);
                        v___y_568_ = v___x_587_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_fst_534_) == 1 {
                    crate::leanh::lean_del_object(v___x_537_);
                    crate::leanh::lean_dec(v_snd_535_);
                    v_val_540_ = crate::leanh::lean_ctor_get(v_fst_534_, 0);
                    crate::leanh::lean_inc(v_val_540_);
                    crate::leanh::lean_dec_ref_known(v_fst_534_, 1);
                    v_packages_541_ = crate::leanh::lean_ctor_get(v_val_540_, 4);
                    v___x_542_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_543_ = lean_array_fget_borrowed(v_packages_541_, v___x_542_);
                    v_config_544_ = crate::leanh::lean_ctor_get(v___x_543_, 6);
                    v_moreGlobalServerArgs_545_ = crate::leanh::lean_ctor_get(v_config_544_, 3);
                    crate::leanh::lean_inc_ref(v_moreGlobalServerArgs_545_);
                    v___x_546_ = l_Lake_Workspace_augmentedEnvVars(v_val_540_);
                    v_fst_508_ = v___x_546_;
                    v_snd_509_ = v_moreGlobalServerArgs_545_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_534_);
                    v___x_547_ = l_Lake_serve___closed__3;
                    v___x_548_ = l_IO_eprintln___at___00Lake_serve_spec__0(v___x_547_);
                    if crate::leanh::lean_obj_tag(v___x_548_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_548_, 1);
                        v_lakeEnv_549_ = crate::leanh::lean_ctor_get(v_config_504_, 0);
                        crate::leanh::lean_inc_ref(v_lakeEnv_549_);
                        v___x_550_ = l_Lake_Env_baseVars(v_lakeEnv_549_);
                        v___x_551_ = l_Lake_invalidConfigEnvVar___closed__0;
                        v___x_552_ = l_Lake_Log_toString(v_snd_535_);
                        crate::leanh::lean_dec(v_snd_535_);
                        v___x_553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_553_, 0, v___x_552_);
                        if v_isShared_538_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_537_, 1, v___x_553_);
                            crate::leanh::lean_ctor_set(v___x_537_, 0, v___x_551_);
                            v___x_555_ = v___x_537_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_551_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_553_);
                            v___x_555_ = v_reuseFailAlloc_558_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_537_);
                        crate::leanh::lean_dec(v_snd_535_);
                        crate::leanh::lean_dec_ref(v_config_504_);
                        v_a_559_ = crate::leanh::lean_ctor_get(v___x_548_, 0);
                        v_isSharedCheck_566_ = (!crate::leanh::lean_is_exclusive(v___x_548_)) as u8;
                        if v_isSharedCheck_566_ == 0 {
                            v___x_561_ = v___x_548_;
                            v_isShared_562_ = v_isSharedCheck_566_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_559_);
                            crate::leanh::lean_dec(v___x_548_);
                            v___x_561_ = crate::leanh::lean_box(0);
                            v_isShared_562_ = v_isSharedCheck_566_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_556_ = lean_array_push(v___x_550_, v___x_555_);
                v___x_557_ = l_Lake_setupFile___closed__3;
                v_fst_508_ = v___x_556_;
                v_snd_509_ = v___x_557_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_562_ == 0 {
                    v___x_564_ = v___x_561_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
                    v___x_564_ = v_reuseFailAlloc_565_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_564_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v___y_568_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_568_, 1);
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_537_);
                    crate::leanh::lean_dec(v_snd_535_);
                    crate::leanh::lean_dec(v_fst_534_);
                    crate::leanh::lean_dec_ref(v_config_504_);
                    v_a_569_ = crate::leanh::lean_ctor_get(v___y_568_, 0);
                    v_isSharedCheck_576_ = (!crate::leanh::lean_is_exclusive(v___y_568_)) as u8;
                    if v_isSharedCheck_576_ == 0 {
                        v___x_571_ = v___y_568_;
                        v_isShared_572_ = v_isSharedCheck_576_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_569_);
                        crate::leanh::lean_dec(v___y_568_);
                        v___x_571_ = crate::leanh::lean_box(0);
                        v_isShared_572_ = v_isSharedCheck_576_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_572_ == 0 {
                    v___x_574_ = v___x_571_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
                    v___x_574_ = v_reuseFailAlloc_575_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_serve___boxed(
    mut v_config_589_: *mut crate::leanh::LeanObject,
    mut v_args_590_: *mut crate::leanh::LeanObject,
    mut v_a_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_592_ = l_Lake_serve(v_config_589_, v_args_590_);
    crate::leanh::lean_dec_ref(v_args_590_);
    return v_res_592_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_CLI_Serve(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Load_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Exit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Run(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Lean_Elab(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_noConfigFileCode = _init_l_Lake_noConfigFileCode();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_CLI_Serve(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_CLI_Serve(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Load_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Exit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Run(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Lean_Elab(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Serve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_CLI_Serve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_CLI_Serve(builtin);
}

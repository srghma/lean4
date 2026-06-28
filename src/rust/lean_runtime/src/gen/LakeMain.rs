// Lean compiler output
// Module: LakeMain
// Imports: Init.System.IO Lake.DSL Lake.CLI.Main
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Lake::CLI::Main::{
    initialize_Lake_CLI_Main, l_Lake_cli, runtime_initialize_Lake_CLI_Main,
};
use crate::r#gen::Lake::DSL::{initialize_Lake_DSL, runtime_initialize_Lake_DSL};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_uint32, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_finalize_task_manager, lean_init_task_manager, lean_initialize,
    lean_initialize_runtime_module, lean_io_mark_end_initialization, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_is_ok, lean_io_result_mk_ok, lean_io_result_show_error,
    lean_mk_string, lean_run_main, lean_setup_args, lean_unbox_uint32,
};
pub unsafe fn _lean_main(mut v_args_9_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_11_: u32 = 0;
    let mut v___x_12_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_13_: *mut LeanObject = core::ptr::null_mut();
    v___x_11_ = l_Lake_cli(v_args_9_);
    v___x_12_ = lean_box_uint32(v___x_11_);
    v___x_13_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_13_, 0, v___x_12_);
    return v___x_13_;
}
pub unsafe fn l_main___boxed(
    mut v_args_14_: *mut LeanObject,
    mut v_a_15_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_16_: *mut LeanObject = core::ptr::null_mut();
    v_res_16_ = _lean_main(v_args_14_);
    return v_res_16_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_LakeMain(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_LakeMain(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_LakeMain(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_DSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_LakeMain(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_LakeMain(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_LakeMain(builtin);
}
unsafe fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut LeanObject {
    let mut args_list = lean_box(0);
    let mut i = argc;
    while i > 1 {
        i -= 1;
        let arg_str = lean_mk_string(*argv.add(i as usize));
        let mut fields = [arg_str, args_list];
        args_list = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(args_list, 0, arg_str);
        lean_ctor_set(args_list, 1, fields[1]);
    }
    return _lean_main(args_list);
}
unsafe fn lean_rust_main(
    argc: core::ffi::c_int,
    mut argv: *mut *mut core::ffi::c_char,
) -> core::ffi::c_int {
    argv = lean_setup_args(argc, argv);
    lean_initialize();
    let res = runtime_initialize_LakeMain(1 /* builtin */);
    lean_io_mark_end_initialization();
    let mut ret_val = 1;
    if lean_io_result_is_ok(res) {
        lean_dec(res);
        lean_init_task_manager();
        let main_res = lean_run_main(run_main, argc, argv);
        lean_finalize_task_manager();
        if lean_io_result_is_ok(main_res) {
            ret_val = lean_unbox_uint32(lean_io_result_get_value(main_res)) as i32;
            lean_dec(main_res);
        } else {
            lean_io_result_show_error(main_res);
            lean_dec(main_res);
        }
    } else {
        lean_io_result_show_error(res);
        lean_dec(res);
    }
    return ret_val;
}

fn main() {
    let c_args: Vec<std::ffi::CString> = std::env::args()
        .map(|arg| std::ffi::CString::new(arg).expect("process argument contains NUL byte"))
        .collect();
    let mut raw_args: Vec<*mut core::ffi::c_char> = c_args
        .iter()
        .map(|arg| arg.as_ptr() as *mut core::ffi::c_char)
        .collect();
    let argc = raw_args.len() as core::ffi::c_int;
    let code = unsafe { lean_rust_main(argc, raw_args.as_mut_ptr()) };
    std::process::exit(code);
}

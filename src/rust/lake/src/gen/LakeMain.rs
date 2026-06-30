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
pub unsafe fn _lean_main(
    mut v_args_9_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_11_: u32 = 0;
    let mut v___x_12_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_13_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_11_ = l_Lake_cli(v_args_9_);
    v___x_12_ = leanh::lean_box_uint32(v___x_11_);
    v___x_13_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_13_, 0, v___x_12_);
    return v___x_13_;
}
pub unsafe fn l_main___boxed(
    mut v_args_14_: *mut leanh::LeanObject,
    mut v_a_15_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_16_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_16_ = _lean_main(v_args_14_);
    return v_res_16_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_LakeMain(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_LakeMain(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_LakeMain(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_CLI_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_LakeMain(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_LakeMain(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_LakeMain(builtin);
}
unsafe fn run_main(
    argc: core::ffi::c_int,
    argv: *mut *mut core::ffi::c_char,
) -> *mut leanh::LeanObject {
    let mut args_list = leanh::lean_box(0);
    let mut i = argc;
    while i > 1 {
        i -= 1;
        let arg_str = leanh::lean_mk_string(*argv.add(i as usize));
        let mut fields = [arg_str, args_list];
        args_list = leanh::lean_alloc_ctor(1, 2, 0);
        leanh::lean_ctor_set(args_list, 0, arg_str);
        leanh::lean_ctor_set(args_list, 1, fields[1]);
    }
    return _lean_main(args_list);
}
unsafe fn lean_rust_main(
    argc: core::ffi::c_int,
    mut argv: *mut *mut core::ffi::c_char,
) -> core::ffi::c_int {
    argv = leanh::lean_setup_args(argc, argv);
    leanh::lean_initialize();
    let res = runtime_initialize_LakeMain(1 /* builtin */);
    leanh::lean_io_mark_end_initialization();
    let mut ret_val = 1;
    if leanh::lean_io_result_is_ok(res) {
        leanh::lean_dec(res);
        leanh::lean_init_task_manager();
        let main_res = leanh::lean_run_main(run_main, argc, argv);
        leanh::lean_finalize_task_manager();
        if leanh::lean_io_result_is_ok(main_res) {
            ret_val =
                leanh::lean_unbox_uint32(leanh::lean_io_result_get_value(main_res))
                    as i32;
            leanh::lean_dec(main_res);
        } else {
            leanh::lean_io_result_show_error(main_res);
            leanh::lean_dec(main_res);
        }
    } else {
        leanh::lean_io_result_show_error(res);
        leanh::lean_dec(res);
    }
    return ret_val;
}

pub fn main() {
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
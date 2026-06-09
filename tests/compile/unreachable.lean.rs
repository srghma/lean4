// Lean compiler output
// Module: unreachable
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
extern "C" {
}
#[no_mangle] pub unsafe extern "C" fn l_False_elim_x27(mut v_C_1_: *mut lean_object, mut v_h_2_: *mut lean_object) -> *mut lean_object{
core::hint::unreachable_unchecked();
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_4_ = lean_box(0);
v___x_5_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_6_: *mut lean_object) -> *mut lean_object{
let mut v_res_7_: *mut lean_object = core::ptr::null_mut(); 
v_res_7_ = _lean_main();
return v_res_7_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_unreachable(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_unreachable(1 /* builtin */);
  lean_io_mark_end_initialization();
  let mut ret_val = 1;
  if lean_io_result_is_ok(res) {
    lean_dec(res);
    lean_init_task_manager();
    let main_res = lean_run_main(run_main, argc, argv);
    lean_finalize_task_manager();
    if lean_io_result_is_ok(main_res) {
      ret_val = 0;
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

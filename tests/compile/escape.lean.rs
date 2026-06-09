// Lean compiler output
// Module: escape
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::System::IO::*;
extern "C" {
}
pub static l_main___closed__0_value: lean_string_object<27> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [13, 102, 97, 105, 108, 101, 100, 32, 97, 116, 32, 99, 111, 117, 110, 116, 101, 114, 45, 101, 120, 97, 109, 112, 108, 101, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
pub static l_main___closed__1_value: lean_string_object<27> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [9, 102, 97, 105, 108, 101, 100, 32, 97, 116, 32, 99, 111, 117, 110, 116, 101, 114, 45, 101, 120, 97, 109, 112, 108, 101, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_4_ = l_main___closed__0;
v___x_5_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_4_);
if lean_obj_tag(v___x_5_) == 0 {
let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_5_, 1);
v___x_6_ = l_main___closed__1;
v___x_7_ = l_IO_eprintln___at___00__private_Init_System_IO_0__IO_eprintlnAux_spec__0(v___x_6_);
return v___x_7_;
} else {
return v___x_5_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_8_: *mut lean_object) -> *mut lean_object{
let mut v_res_9_: *mut lean_object = core::ptr::null_mut(); 
v_res_9_ = _lean_main();
return v_res_9_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_escape(builtin: u8) -> *mut lean_object {
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
  let res = initialize_escape(1 /* builtin */);
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

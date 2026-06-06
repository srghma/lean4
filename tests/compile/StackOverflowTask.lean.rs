// Lean compiler output
// Module: StackOverflowTask
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_task_spawn(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_task_get_own(_: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
static mut l_main___lam__0___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___lam__0___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_foo(mut v_x_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); 
v___x_2_ = l_foo(v_x_1_);
v___x_3_ = lean_unsigned_to_nat(1);
v___x_4_ = lean_nat_add(v___x_2_, v___x_3_);
lean_dec(v___x_2_);
return v___x_4_;
}
#[no_mangle] pub unsafe extern "C" fn l_foo___boxed(mut v_x_5_: *mut lean_object) -> *mut lean_object{
let mut v_res_6_: *mut lean_object = core::ptr::null_mut(); 
v_res_6_ = l_foo(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___lam__0___closed__0() -> *mut lean_object{
let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); 
v___x_7_ = lean_unsigned_to_nat(0);
v___x_8_ = l_foo(v___x_7_);
return v___x_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v_x_9_: *mut lean_object) -> *mut lean_object{
let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); 
v___x_10_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___lam__0___closed__0), core::ptr::addr_of_mut!(l_main___lam__0___closed__0_once), _init_l_main___lam__0___closed__0);
return v___x_10_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_11_: *mut lean_object) -> *mut lean_object{
let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_13_ = lean_get_stdout();
v_putStr_14_ = lean_ctor_get(v___x_13_, 4);
lean_inc_ref(v_putStr_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lean_apply_2(v_putStr_14_, v_s_11_, lean_box(0));
return v___x_15_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_16_: *mut lean_object, mut v_a_17_: *mut lean_object) -> *mut lean_object{
let mut v_res_18_: *mut lean_object = core::ptr::null_mut(); 
v_res_18_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_16_);
return v_res_18_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_19_: *mut lean_object) -> *mut lean_object{
let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: u32 = 0; let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); 
v___x_21_ = l_Nat_reprFast(v_s_19_);
v___x_22_ = 10;
v___x_23_ = lean_string_push(v___x_21_, v___x_22_);
v___x_24_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_23_);
return v___x_24_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_25_: *mut lean_object, mut v_a_26_: *mut lean_object) -> *mut lean_object{
let mut v_res_27_: *mut lean_object = core::ptr::null_mut(); 
v_res_27_ = l_IO_println___at___00main_spec__0(v_s_25_);
return v_res_27_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___f_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); 
v___f_29_ = lean_alloc_closure(l_main___lam__0 as *mut core::ffi::c_void, 1, 0);
v___x_30_ = lean_unsigned_to_nat(0);
v___x_31_ = lean_task_spawn(v___f_29_, v___x_30_);
v___x_32_ = lean_task_get_own(v___x_31_);
v___x_33_ = l_IO_println___at___00main_spec__0(v___x_32_);
return v___x_33_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_34_: *mut lean_object) -> *mut lean_object{
let mut v_res_35_: *mut lean_object = core::ptr::null_mut(); 
v_res_35_ = _lean_main();
return v_res_35_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_StackOverflowTask(builtin: u8) -> *mut lean_object {
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
  let res = initialize_StackOverflowTask(1 /* builtin */);
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

// Lean compiler output
// Module: bigctor
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_mkFoo(mut v_x_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); 
v___x_2_ = lean_unsigned_to_nat(0);
v___x_3_ = lean_alloc_ctor(0, 70, (0) as u32);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_2_);
lean_ctor_set(v___x_3_, 2, v___x_2_);
lean_ctor_set(v___x_3_, 3, v___x_2_);
lean_ctor_set(v___x_3_, 4, v___x_2_);
lean_ctor_set(v___x_3_, 5, v___x_2_);
lean_ctor_set(v___x_3_, 6, v___x_2_);
lean_ctor_set(v___x_3_, 7, v___x_2_);
lean_ctor_set(v___x_3_, 8, v___x_2_);
lean_ctor_set(v___x_3_, 9, v___x_2_);
lean_ctor_set(v___x_3_, 10, v___x_2_);
lean_ctor_set(v___x_3_, 11, v___x_2_);
lean_ctor_set(v___x_3_, 12, v___x_2_);
lean_ctor_set(v___x_3_, 13, v___x_2_);
lean_ctor_set(v___x_3_, 14, v___x_2_);
lean_ctor_set(v___x_3_, 15, v___x_2_);
lean_ctor_set(v___x_3_, 16, v___x_2_);
lean_ctor_set(v___x_3_, 17, v___x_2_);
lean_ctor_set(v___x_3_, 18, v___x_2_);
lean_ctor_set(v___x_3_, 19, v___x_2_);
lean_ctor_set(v___x_3_, 20, v___x_2_);
lean_ctor_set(v___x_3_, 21, v___x_2_);
lean_ctor_set(v___x_3_, 22, v___x_2_);
lean_ctor_set(v___x_3_, 23, v___x_2_);
lean_ctor_set(v___x_3_, 24, v___x_2_);
lean_ctor_set(v___x_3_, 25, v___x_2_);
lean_ctor_set(v___x_3_, 26, v___x_2_);
lean_ctor_set(v___x_3_, 27, v___x_2_);
lean_ctor_set(v___x_3_, 28, v___x_2_);
lean_ctor_set(v___x_3_, 29, v___x_2_);
lean_ctor_set(v___x_3_, 30, v___x_2_);
lean_ctor_set(v___x_3_, 31, v___x_2_);
lean_ctor_set(v___x_3_, 32, v___x_2_);
lean_ctor_set(v___x_3_, 33, v___x_2_);
lean_ctor_set(v___x_3_, 34, v___x_2_);
lean_ctor_set(v___x_3_, 35, v___x_2_);
lean_ctor_set(v___x_3_, 36, v___x_2_);
lean_ctor_set(v___x_3_, 37, v___x_2_);
lean_ctor_set(v___x_3_, 38, v___x_2_);
lean_ctor_set(v___x_3_, 39, v___x_2_);
lean_ctor_set(v___x_3_, 40, v___x_2_);
lean_ctor_set(v___x_3_, 41, v___x_2_);
lean_ctor_set(v___x_3_, 42, v___x_2_);
lean_ctor_set(v___x_3_, 43, v___x_2_);
lean_ctor_set(v___x_3_, 44, v___x_2_);
lean_ctor_set(v___x_3_, 45, v___x_2_);
lean_ctor_set(v___x_3_, 46, v___x_2_);
lean_ctor_set(v___x_3_, 47, v___x_2_);
lean_ctor_set(v___x_3_, 48, v___x_2_);
lean_ctor_set(v___x_3_, 49, v___x_2_);
lean_ctor_set(v___x_3_, 50, v___x_2_);
lean_ctor_set(v___x_3_, 51, v___x_2_);
lean_ctor_set(v___x_3_, 52, v___x_2_);
lean_ctor_set(v___x_3_, 53, v___x_2_);
lean_ctor_set(v___x_3_, 54, v___x_2_);
lean_ctor_set(v___x_3_, 55, v___x_2_);
lean_ctor_set(v___x_3_, 56, v___x_2_);
lean_ctor_set(v___x_3_, 57, v___x_2_);
lean_ctor_set(v___x_3_, 58, v___x_2_);
lean_ctor_set(v___x_3_, 59, v_x_1_);
lean_ctor_set(v___x_3_, 60, v___x_2_);
lean_ctor_set(v___x_3_, 61, v___x_2_);
lean_ctor_set(v___x_3_, 62, v___x_2_);
lean_ctor_set(v___x_3_, 63, v___x_2_);
lean_ctor_set(v___x_3_, 64, v___x_2_);
lean_ctor_set(v___x_3_, 65, v___x_2_);
lean_ctor_set(v___x_3_, 66, v___x_2_);
lean_ctor_set(v___x_3_, 67, v___x_2_);
lean_ctor_set(v___x_3_, 68, v___x_2_);
lean_ctor_set(v___x_3_, 69, v___x_2_);
return v___x_3_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_4_: *mut lean_object) -> *mut lean_object{
let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_7_: *mut lean_object = core::ptr::null_mut(); let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); 
v___x_6_ = lean_get_stdout();
v_putStr_7_ = lean_ctor_get(v___x_6_, 4);
lean_inc_ref(v_putStr_7_);
lean_dec_ref(v___x_6_);
v___x_8_ = lean_apply_2(v_putStr_7_, v_s_4_, lean_box(0));
return v___x_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_9_: *mut lean_object, mut v_a_10_: *mut lean_object) -> *mut lean_object{
let mut v_res_11_: *mut lean_object = core::ptr::null_mut(); 
v_res_11_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_9_);
return v_res_11_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_12_: *mut lean_object) -> *mut lean_object{
let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: u32 = 0; let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); 
v___x_14_ = l_Nat_reprFast(v_s_12_);
v___x_15_ = 10;
v___x_16_ = lean_string_push(v___x_14_, v___x_15_);
v___x_17_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_16_);
return v___x_17_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_18_: *mut lean_object, mut v_a_19_: *mut lean_object) -> *mut lean_object{
let mut v_res_20_: *mut lean_object = core::ptr::null_mut(); 
v_res_20_ = l_IO_println___at___00main_spec__0(v_s_18_);
return v_res_20_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> *mut lean_object{
let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); 
v___x_21_ = lean_unsigned_to_nat(10);
v___x_22_ = l_mkFoo(v___x_21_);
return v___x_22_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v_yy10_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); 
v___x_24_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v_yy10_25_ = lean_ctor_get(v___x_24_, 59);
lean_inc(v_yy10_25_);
v___x_26_ = l_IO_println___at___00main_spec__0(v_yy10_25_);
return v___x_26_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_27_: *mut lean_object) -> *mut lean_object{
let mut v_res_28_: *mut lean_object = core::ptr::null_mut(); 
v_res_28_ = _lean_main();
return v_res_28_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_bigctor(builtin: u8) -> *mut lean_object {
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
  let res = initialize_bigctor(1 /* builtin */);
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

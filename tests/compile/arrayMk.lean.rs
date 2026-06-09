// Lean compiler output
// Module: arrayMk
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::List::Basic::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Defs::*;
extern "C" {
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_array_mk(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
static mut l_step___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_step___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_step___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_step___closed__1: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_step: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn _init_l_step___closed__0() -> *mut lean_object{
let mut v___x_1_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); 
v___x_1_ = lean_unsigned_to_nat(10);
v___x_2_ = l_List_range(v___x_1_);
return v___x_2_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_step___closed__1() -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_obj_once(core::ptr::addr_of_mut!(l_step___closed__0), core::ptr::addr_of_mut!(l_step___closed__0_once), _init_l_step___closed__0);
v___x_4_ = lean_array_mk(v___x_3_);
return v___x_4_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_step() -> *mut lean_object{
let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_5_ = lean_obj_once(core::ptr::addr_of_mut!(l_step___closed__1), core::ptr::addr_of_mut!(l_step___closed__1_once), _init_l_step___closed__1);
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00main_spec__0(mut v_s_6_: *mut lean_object) -> *mut lean_object{
let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); 
v___x_8_ = lean_get_stdout();
v_putStr_9_ = lean_ctor_get(v___x_8_, 4);
lean_inc_ref(v_putStr_9_);
lean_dec_ref(v___x_8_);
v___x_10_ = lean_apply_2(v_putStr_9_, v_s_6_, lean_box(0));
return v___x_10_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00main_spec__0___boxed(mut v_s_11_: *mut lean_object, mut v_a_12_: *mut lean_object) -> *mut lean_object{
let mut v_res_13_: *mut lean_object = core::ptr::null_mut(); 
v_res_13_ = l_IO_print___at___00main_spec__0(v_s_11_);
return v_res_13_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> *mut lean_object{
let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_14_ = l_step;
v___x_15_ = lean_array_get_size(v___x_14_);
return v___x_15_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); 
v___x_16_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v___x_17_ = l_Nat_reprFast(v___x_16_);
return v___x_17_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> *mut lean_object{
let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); 
v___x_19_ = l_main___closed__2;
v___x_20_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_21_ = lean_string_append(v___x_20_, v___x_19_);
return v___x_21_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); 
v___x_23_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_24_ = l_IO_print___at___00main_spec__0(v___x_23_);
return v___x_24_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_25_: *mut lean_object) -> *mut lean_object{
let mut v_res_26_: *mut lean_object = core::ptr::null_mut(); 
v_res_26_ = _lean_main();
return v_res_26_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_arrayMk(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_step = _init_l_step();
lean_mark_persistent(l_step);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_arrayMk(1 /* builtin */);
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

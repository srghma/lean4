// Lean compiler output
// Module: tuple
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_main___closed__0_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut lean_object,((( 3 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_f(mut v_a_1_: *mut lean_object) -> *mut lean_object{
let mut v_snd_2_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_3_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_4_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_5_: *mut lean_object = core::ptr::null_mut(); let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); 
v_snd_2_ = lean_ctor_get(v_a_1_, 1);
v_fst_3_ = lean_ctor_get(v_a_1_, 0);
v_fst_4_ = lean_ctor_get(v_snd_2_, 0);
v_snd_5_ = lean_ctor_get(v_snd_2_, 1);
v___x_6_ = lean_nat_add(v_fst_3_, v_fst_4_);
v___x_7_ = lean_nat_add(v___x_6_, v_snd_5_);
lean_dec(v___x_6_);
return v___x_7_;
}
#[no_mangle] pub unsafe extern "C" fn l_f___boxed(mut v_a_8_: *mut lean_object) -> *mut lean_object{
let mut v_res_9_: *mut lean_object = core::ptr::null_mut(); 
v_res_9_ = l_f(v_a_8_);
lean_dec_ref(v_a_8_);
return v_res_9_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_10_: *mut lean_object) -> *mut lean_object{
let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); 
v___x_12_ = lean_get_stdout();
v_putStr_13_ = lean_ctor_get(v___x_12_, 4);
lean_inc_ref(v_putStr_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lean_apply_2(v_putStr_13_, v_s_10_, lean_box(0));
return v___x_14_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_15_: *mut lean_object, mut v_a_16_: *mut lean_object) -> *mut lean_object{
let mut v_res_17_: *mut lean_object = core::ptr::null_mut(); 
v_res_17_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_15_);
return v_res_17_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_18_: *mut lean_object) -> *mut lean_object{
let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: u32 = 0; let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); 
v___x_20_ = l_Nat_reprFast(v_s_18_);
v___x_21_ = 10;
v___x_22_ = lean_string_push(v___x_20_, v___x_21_);
v___x_23_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_22_);
return v___x_23_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_24_: *mut lean_object, mut v_a_25_: *mut lean_object) -> *mut lean_object{
let mut v_res_26_: *mut lean_object = core::ptr::null_mut(); 
v_res_26_ = l_IO_println___at___00main_spec__0(v_s_24_);
return v_res_26_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); 
v___x_33_ = l_main___closed__1;
v___x_34_ = l_f(v___x_33_);
return v___x_34_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); 
v___x_36_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_37_ = l_IO_println___at___00main_spec__0(v___x_36_);
return v___x_37_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_38_: *mut lean_object) -> *mut lean_object{
let mut v_res_39_: *mut lean_object = core::ptr::null_mut(); 
v_res_39_ = _lean_main();
return v_res_39_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_tuple(builtin: u8) -> *mut lean_object {
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
  let res = initialize_tuple(1 /* builtin */);
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

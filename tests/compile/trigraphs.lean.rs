// Lean compiler output
// Module: trigraphs
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
pub static l_main___closed__0_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [63, 63, 40, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
pub static l_main___closed__1_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [63, 63, 41, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
pub static l_main___closed__2_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [63, 63, 60, 0]};
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
pub static l_main___closed__3_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [63, 63, 62, 0]};
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
pub static l_main___closed__4_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [63, 63, 61, 0]};
static mut l_main___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object;
pub static l_main___closed__5_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [63, 63, 47, 0]};
static mut l_main___closed__5: *mut lean_object = core::ptr::addr_of!(l_main___closed__5_value) as *mut lean_object;
pub static l_main___closed__6_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [63, 63, 39, 0]};
static mut l_main___closed__6: *mut lean_object = core::ptr::addr_of!(l_main___closed__6_value) as *mut lean_object;
pub static l_main___closed__7_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [63, 63, 33, 0]};
static mut l_main___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object;
pub static l_main___closed__8_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [63, 63, 45, 0]};
static mut l_main___closed__8: *mut lean_object = core::ptr::addr_of!(l_main___closed__8_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_get_stdout();
v_putStr_4_ = lean_ctor_get(v___x_3_, 4);
lean_inc_ref(v_putStr_4_);
lean_dec_ref(v___x_3_);
v___x_5_ = lean_apply_2(v_putStr_4_, v_s_1_, lean_box(0));
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_6_: *mut lean_object, mut v_a_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_6_);
return v_res_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_9_: *mut lean_object) -> *mut lean_object{
let mut v___x_11_: u32 = 0; let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = 10;
v___x_12_ = lean_string_push(v_s_9_, v___x_11_);
v___x_13_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_12_);
return v___x_13_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_14_: *mut lean_object, mut v_a_15_: *mut lean_object) -> *mut lean_object{
let mut v_res_16_: *mut lean_object = core::ptr::null_mut(); 
v_res_16_ = l_IO_println___at___00main_spec__0(v_s_14_);
return v_res_16_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); 
v___x_27_ = l_main___closed__0;
v___x_28_ = l_IO_println___at___00main_spec__0(v___x_27_);
if lean_obj_tag(v___x_28_) == 0 {
let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_28_, 1);
v___x_29_ = l_main___closed__1;
v___x_30_ = l_IO_println___at___00main_spec__0(v___x_29_);
if lean_obj_tag(v___x_30_) == 0 {
let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_30_, 1);
v___x_31_ = l_main___closed__2;
v___x_32_ = l_IO_println___at___00main_spec__0(v___x_31_);
if lean_obj_tag(v___x_32_) == 0 {
let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_32_, 1);
v___x_33_ = l_main___closed__3;
v___x_34_ = l_IO_println___at___00main_spec__0(v___x_33_);
if lean_obj_tag(v___x_34_) == 0 {
let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_34_, 1);
v___x_35_ = l_main___closed__4;
v___x_36_ = l_IO_println___at___00main_spec__0(v___x_35_);
if lean_obj_tag(v___x_36_) == 0 {
let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_36_, 1);
v___x_37_ = l_main___closed__5;
v___x_38_ = l_IO_println___at___00main_spec__0(v___x_37_);
if lean_obj_tag(v___x_38_) == 0 {
let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_38_, 1);
v___x_39_ = l_main___closed__6;
v___x_40_ = l_IO_println___at___00main_spec__0(v___x_39_);
if lean_obj_tag(v___x_40_) == 0 {
let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_40_, 1);
v___x_41_ = l_main___closed__7;
v___x_42_ = l_IO_println___at___00main_spec__0(v___x_41_);
if lean_obj_tag(v___x_42_) == 0 {
let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_42_, 1);
v___x_43_ = l_main___closed__8;
v___x_44_ = l_IO_println___at___00main_spec__0(v___x_43_);
return v___x_44_;
} else {
return v___x_42_;
}
} else {
return v___x_40_;
}
} else {
return v___x_38_;
}
} else {
return v___x_36_;
}
} else {
return v___x_34_;
}
} else {
return v___x_32_;
}
} else {
return v___x_30_;
}
} else {
return v___x_28_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_45_: *mut lean_object) -> *mut lean_object{
let mut v_res_46_: *mut lean_object = core::ptr::null_mut(); 
v_res_46_ = _lean_main();
return v_res_46_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_trigraphs(builtin: u8) -> *mut lean_object {
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
  let res = initialize_trigraphs(1 /* builtin */);
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

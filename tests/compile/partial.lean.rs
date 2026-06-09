// Lean compiler output
// Module: partial
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Data::String::Basic::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_utf8_get(_: *mut lean_object, _: *mut lean_object) -> u32;
    fn lean_string_utf8_next(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
pub static l_IO_println___at___00main_spec__0___closed__0_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_IO_println___at___00main_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__0___closed__0_value) as *mut lean_object;
pub static l_IO_println___at___00main_spec__0___closed__1_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_IO_println___at___00main_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__0___closed__1_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 101, 108, 108, 111, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: u8 = 0;
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: u8 = 0;
#[no_mangle] pub unsafe extern "C" fn l_contains(mut v_x_1_: *mut lean_object, mut v_x_2_: u32, mut v_x_3_: *mut lean_object) -> u8{
let mut v___x_4_: u8 = 0; let mut v___x_5_: u32 = 0; let mut v___x_6_: u8 = 0; let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_4_ = lean_string_utf8_at_end(v_x_1_, v_x_3_);
if v___x_4_ == 0 {
v___x_5_ = lean_string_utf8_get(v_x_1_, v_x_3_);
v___x_6_ = lean_uint32_dec_eq(v___x_5_, v_x_2_);
if v___x_6_ == 0 {
v___x_7_ = lean_string_utf8_next(v_x_1_, v_x_3_);
lean_dec(v_x_3_);
v_x_3_ = v___x_7_;
state = 0; continue;
} else {
lean_dec(v_x_3_);
return v___x_6_;
}
} else {
lean_dec(v_x_3_);
v___x_9_ = 0;
return v___x_9_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_contains___boxed(mut v_x_10_: *mut lean_object, mut v_x_11_: *mut lean_object, mut v_x_12_: *mut lean_object) -> *mut lean_object{
let mut v_x_107__boxed_13_: u32 = 0; let mut v_res_14_: u8 = 0; let mut v_r_15_: *mut lean_object = core::ptr::null_mut(); 
v_x_107__boxed_13_ = lean_unbox_uint32(v_x_11_);
lean_dec(v_x_11_);
v_res_14_ = l_contains(v_x_10_, v_x_107__boxed_13_, v_x_12_);
lean_dec_ref(v_x_10_);
v_r_15_ = lean_box((v_res_14_) as usize);
return v_r_15_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_16_: *mut lean_object) -> *mut lean_object{
let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_19_: *mut lean_object = core::ptr::null_mut(); let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); 
v___x_18_ = lean_get_stdout();
v_putStr_19_ = lean_ctor_get(v___x_18_, 4);
lean_inc_ref(v_putStr_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lean_apply_2(v_putStr_19_, v_s_16_, lean_box(0));
return v___x_20_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_21_: *mut lean_object, mut v_a_22_: *mut lean_object) -> *mut lean_object{
let mut v_res_23_: *mut lean_object = core::ptr::null_mut(); 
v_res_23_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_21_);
return v_res_23_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_26_: u8) -> *mut lean_object{
let mut v___y_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_30_: u32 = 0; let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if v_s_26_ == 0 {
v___x_33_ = l_IO_println___at___00main_spec__0___closed__0;
v___y_29_ = v___x_33_;
state = 1; continue;
} else {
v___x_34_ = l_IO_println___at___00main_spec__0___closed__1;
v___y_29_ = v___x_34_;
state = 1; continue;
}
}
1 => {
v___x_30_ = 10;
lean_inc_ref(v___y_29_);
v___x_31_ = lean_string_push(v___y_29_, v___x_30_);
v___x_32_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_31_);
return v___x_32_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_35_: *mut lean_object, mut v_a_36_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_37_: u8 = 0; let mut v_res_38_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_37_ = (lean_unbox(v_s_35_) as u8);
v_res_38_ = l_IO_println___at___00main_spec__0(v_s_boxed_37_);
return v_res_38_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> u8{
let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: u32 = 0; let mut v_s1_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: u8 = 0; 
v___x_40_ = lean_unsigned_to_nat(0);
v___x_41_ = 97;
v_s1_42_ = l_main___closed__0;
v___x_43_ = l_contains(v_s1_42_, v___x_41_, v___x_40_);
return v___x_43_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> u8{
let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: u32 = 0; let mut v_s1_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: u8 = 0; 
v___x_44_ = lean_unsigned_to_nat(0);
v___x_45_ = 111;
v_s1_46_ = l_main___closed__0;
v___x_47_ = l_contains(v_s1_46_, v___x_45_, v___x_44_);
return v___x_47_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_49_: u8 = 0; let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); 
v___x_49_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_50_ = l_IO_println___at___00main_spec__0(v___x_49_);
if lean_obj_tag(v___x_50_) == 0 {
let mut v___x_51_: u8 = 0; let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_50_, 1);
v___x_51_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_52_ = l_IO_println___at___00main_spec__0(v___x_51_);
return v___x_52_;
} else {
return v___x_50_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_53_: *mut lean_object) -> *mut lean_object{
let mut v_res_54_: *mut lean_object = core::ptr::null_mut(); 
v_res_54_ = _lean_main();
return v_res_54_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_partial(builtin: u8) -> *mut lean_object {
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
  let res = initialize_partial(1 /* builtin */);
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

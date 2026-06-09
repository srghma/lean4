// Lean compiler output
// Module: strictAndOr
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Core::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
pub static l_IO_println___at___00main_spec__0___closed__0_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_IO_println___at___00main_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__0___closed__0_value) as *mut lean_object;
pub static l_IO_println___at___00main_spec__0___closed__1_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_IO_println___at___00main_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__0___closed__1_value) as *mut lean_object;
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: u8 = 0;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: u8 = 0;
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: u8 = 0;
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: u8 = 0;
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: u8 = 0;
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: u8 = 0;
static mut l_main___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__6: u8 = 0;
static mut l_main___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__7: u8 = 0;
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
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_11_: u8) -> *mut lean_object{
let mut v___y_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: u32 = 0; let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if v_s_11_ == 0 {
v___x_18_ = l_IO_println___at___00main_spec__0___closed__0;
v___y_14_ = v___x_18_;
state = 1; continue;
} else {
v___x_19_ = l_IO_println___at___00main_spec__0___closed__1;
v___y_14_ = v___x_19_;
state = 1; continue;
}
}
1 => {
v___x_15_ = 10;
lean_inc_ref(v___y_14_);
v___x_16_ = lean_string_push(v___y_14_, v___x_15_);
v___x_17_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_16_);
return v___x_17_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_20_: *mut lean_object, mut v_a_21_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_22_: u8 = 0; let mut v_res_23_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_22_ = (lean_unbox(v_s_20_) as u8);
v_res_23_ = l_IO_println___at___00main_spec__0(v_s_boxed_22_);
return v_res_23_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> u8{
let mut v___x_24_: u8 = 0; let mut v___x_25_: u8 = 0; let mut v___x_26_: u8 = 0; 
v___x_24_ = 0;
v___x_25_ = 1;
v___x_26_ = lean_strict_or(v___x_25_, v___x_24_);
return v___x_26_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> u8{
let mut v___x_27_: u8 = 0; let mut v___x_28_: u8 = 0; 
v___x_27_ = 1;
v___x_28_ = lean_strict_or(v___x_27_, v___x_27_);
return v___x_28_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> u8{
let mut v___x_29_: u8 = 0; let mut v___x_30_: u8 = 0; 
v___x_29_ = 0;
v___x_30_ = lean_strict_and(v___x_29_, v___x_29_);
return v___x_30_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> u8{
let mut v___x_31_: u8 = 0; let mut v___x_32_: u8 = 0; let mut v___x_33_: u8 = 0; 
v___x_31_ = 1;
v___x_32_ = 0;
v___x_33_ = lean_strict_and(v___x_32_, v___x_31_);
return v___x_33_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> u8{
let mut v___x_34_: u8 = 0; let mut v___x_35_: u8 = 0; let mut v___x_36_: u8 = 0; 
v___x_34_ = 0;
v___x_35_ = 1;
v___x_36_ = lean_strict_and(v___x_35_, v___x_34_);
return v___x_36_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> u8{
let mut v___x_37_: u8 = 0; let mut v___x_38_: u8 = 0; 
v___x_37_ = 1;
v___x_38_ = lean_strict_and(v___x_37_, v___x_37_);
return v___x_38_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> u8{
let mut v___x_39_: u8 = 0; let mut v___x_40_: u8 = 0; 
v___x_39_ = 0;
v___x_40_ = lean_strict_or(v___x_39_, v___x_39_);
return v___x_40_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__7() -> u8{
let mut v___x_41_: u8 = 0; let mut v___x_42_: u8 = 0; let mut v___x_43_: u8 = 0; 
v___x_41_ = 1;
v___x_42_ = 0;
v___x_43_ = lean_strict_or(v___x_42_, v___x_41_);
return v___x_43_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___y_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: u8 = 0; let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: u8 = 0; let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: u8 = 0; let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: u8 = 0; let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: u8 = 0; let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: u8 = 0; let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: u8 = 0; let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: u8 = 0; let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_59_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v___x_60_ = l_IO_println___at___00main_spec__0(v___x_59_);
if lean_obj_tag(v___x_60_) == 0 {
lean_dec_ref_known(v___x_60_, 1);
v___x_61_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_62_ = l_IO_println___at___00main_spec__0(v___x_61_);
v___y_46_ = v___x_62_;
state = 1; continue;
} else {
v___y_46_ = v___x_60_;
state = 1; continue;
}
}
1 => {
if lean_obj_tag(v___y_46_) == 0 {
lean_dec_ref_known(v___y_46_, 1);
v___x_47_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v___x_48_ = l_IO_println___at___00main_spec__0(v___x_47_);
if lean_obj_tag(v___x_48_) == 0 {
lean_dec_ref_known(v___x_48_, 1);
v___x_49_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_50_ = l_IO_println___at___00main_spec__0(v___x_49_);
if lean_obj_tag(v___x_50_) == 0 {
lean_dec_ref_known(v___x_50_, 1);
v___x_51_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_52_ = l_IO_println___at___00main_spec__0(v___x_51_);
if lean_obj_tag(v___x_52_) == 0 {
lean_dec_ref_known(v___x_52_, 1);
v___x_53_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_54_ = l_IO_println___at___00main_spec__0(v___x_53_);
if lean_obj_tag(v___x_54_) == 0 {
lean_dec_ref_known(v___x_54_, 1);
v___x_55_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___x_56_ = l_IO_println___at___00main_spec__0(v___x_55_);
if lean_obj_tag(v___x_56_) == 0 {
lean_dec_ref_known(v___x_56_, 1);
v___x_57_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_58_ = l_IO_println___at___00main_spec__0(v___x_57_);
return v___x_58_;
} else {
return v___x_56_;
}
} else {
return v___x_54_;
}
} else {
return v___x_52_;
}
} else {
return v___x_50_;
}
} else {
return v___x_48_;
}
} else {
return v___y_46_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_63_: *mut lean_object) -> *mut lean_object{
let mut v_res_64_: *mut lean_object = core::ptr::null_mut(); 
v_res_64_ = _lean_main();
return v_res_64_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_strictAndOr(builtin: u8) -> *mut lean_object {
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
  let res = initialize_strictAndOr(1 /* builtin */);
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

// Lean compiler output
// Module: «534»
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Data::UInt::BasicAux::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::Array::Basic::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
pub static l_foo___closed__0_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_foo___closed__0: *mut lean_object = core::ptr::addr_of!(l_foo___closed__0_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [104, 105, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0(mut v_as_1_: *mut lean_object, mut v_i_2_: usize, mut v_stop_3_: usize, mut v_b_4_: *mut lean_object) -> *mut lean_object{
let mut v___y_6_: *mut lean_object = core::ptr::null_mut(); let mut v___x_7_: usize = 0; let mut v___x_8_: usize = 0; let mut v___x_10_: u8 = 0; let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: u8 = 0; let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_10_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if v___x_10_ == 0 {
v___x_11_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v___x_12_ = lean_unsigned_to_nat(5);
v___x_13_ = lean_nat_dec_eq(v___x_11_, v___x_12_);
if v___x_13_ == 0 {
lean_inc(v___x_11_);
v___x_14_ = lean_array_push(v_b_4_, v___x_11_);
v___y_6_ = v___x_14_;
state = 1; continue;
} else {
v___y_6_ = v_b_4_;
state = 1; continue;
}
} else {
return v_b_4_;
}
}
1 => {
v___x_7_ = 1usize;
v___x_8_ = lean_usize_add(v_i_2_, v___x_7_);
v_i_2_ = v___x_8_;
v_b_4_ = v___y_6_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0___boxed(mut v_as_15_: *mut lean_object, mut v_i_16_: *mut lean_object, mut v_stop_17_: *mut lean_object, mut v_b_18_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_19_: usize = 0; let mut v_stop_boxed_20_: usize = 0; let mut v_res_21_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_19_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_stop_boxed_20_ = lean_unbox_usize(v_stop_17_);
lean_dec(v_stop_17_);
v_res_21_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0(v_as_15_, v_i_boxed_19_, v_stop_boxed_20_, v_b_18_);
lean_dec_ref(v_as_15_);
return v_res_21_;
}
#[no_mangle] pub unsafe extern "C" fn l_foo(mut v_array_24_: *mut lean_object, mut v_x_25_: *mut lean_object) -> *mut lean_object{
let mut v_zero_26_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_27_: u8 = 0; let mut v_one_28_: *mut lean_object = core::ptr::null_mut(); let mut v_n_29_: *mut lean_object = core::ptr::null_mut(); let mut v___y_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: u8 = 0; let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v_arrayOfLast_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: u8 = 0; let mut v___x_42_: u8 = 0; let mut v___x_43_: usize = 0; let mut v___x_44_: usize = 0; let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); let mut v___x_46_: usize = 0; let mut v___x_47_: usize = 0; let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_26_ = lean_unsigned_to_nat(0);
v_isZero_27_ = lean_nat_dec_eq(v_x_25_, v_zero_26_);
if v_isZero_27_ == 1 {
lean_dec(v_x_25_);
lean_dec_ref(v_array_24_);
return v_zero_26_;
} else {
v_one_28_ = lean_unsigned_to_nat(1);
v_n_29_ = lean_nat_sub(v_x_25_, v_one_28_);
lean_dec(v_x_25_);
v___x_39_ = lean_array_get_size(v_array_24_);
v___x_40_ = l_foo___closed__0;
v___x_41_ = lean_nat_dec_lt(v_zero_26_, v___x_39_);
if v___x_41_ == 0 {
lean_dec_ref(v_array_24_);
v___y_31_ = v___x_40_;
state = 1; continue;
} else {
v___x_42_ = lean_nat_dec_le(v___x_39_, v___x_39_);
if v___x_42_ == 0 {
if v___x_41_ == 0 {
lean_dec_ref(v_array_24_);
v___y_31_ = v___x_40_;
state = 1; continue;
} else {
v___x_43_ = 0usize;
v___x_44_ = lean_usize_of_nat(v___x_39_);
v___x_45_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0(v_array_24_, v___x_43_, v___x_44_, v___x_40_);
lean_dec_ref(v_array_24_);
v___y_31_ = v___x_45_;
state = 1; continue;
}
} else {
v___x_46_ = 0usize;
v___x_47_ = lean_usize_of_nat(v___x_39_);
v___x_48_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00foo_spec__0(v_array_24_, v___x_46_, v___x_47_, v___x_40_);
lean_dec_ref(v_array_24_);
v___y_31_ = v___x_48_;
state = 1; continue;
}
}
}
}
1 => {
v___x_32_ = lean_array_get_size(v___y_31_);
v___x_33_ = lean_nat_dec_eq(v___x_32_, v_zero_26_);
if v___x_33_ == 0 {
v___x_34_ = lean_nat_sub(v___x_32_, v_one_28_);
v___x_35_ = lean_array_get(v_zero_26_, v___y_31_, v___x_34_);
lean_dec(v___x_34_);
lean_dec_ref(v___y_31_);
v___x_36_ = lean_mk_empty_array_with_capacity(v_one_28_);
v_arrayOfLast_37_ = lean_array_push(v___x_36_, v___x_35_);
v_array_24_ = v_arrayOfLast_37_;
v_x_25_ = v_n_29_;
state = 0; continue;
} else {
lean_dec_ref(v___y_31_);
lean_dec(v_n_29_);
return v_zero_26_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_49_: *mut lean_object) -> *mut lean_object{
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); 
v___x_51_ = lean_get_stdout();
v_putStr_52_ = lean_ctor_get(v___x_51_, 4);
lean_inc_ref(v_putStr_52_);
lean_dec_ref(v___x_51_);
v___x_53_ = lean_apply_2(v_putStr_52_, v_s_49_, lean_box(0));
return v___x_53_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_54_: *mut lean_object, mut v_a_55_: *mut lean_object) -> *mut lean_object{
let mut v_res_56_: *mut lean_object = core::ptr::null_mut(); 
v_res_56_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_54_);
return v_res_56_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_57_: *mut lean_object) -> *mut lean_object{
let mut v___x_59_: u32 = 0; let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); 
v___x_59_ = 10;
v___x_60_ = lean_string_push(v_s_57_, v___x_59_);
v___x_61_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_60_);
return v___x_61_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_62_: *mut lean_object, mut v_a_63_: *mut lean_object) -> *mut lean_object{
let mut v_res_64_: *mut lean_object = core::ptr::null_mut(); 
v_res_64_ = l_IO_println___at___00main_spec__0(v_s_62_);
return v_res_64_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); 
v___x_67_ = l_main___closed__0;
v___x_68_ = l_IO_println___at___00main_spec__0(v___x_67_);
return v___x_68_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_69_: *mut lean_object) -> *mut lean_object{
let mut v_res_70_: *mut lean_object = core::ptr::null_mut(); 
v_res_70_ = _lean_main();
return v_res_70_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_00534(builtin: u8) -> *mut lean_object {
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
  let res = initialize_00534(1 /* builtin */);
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

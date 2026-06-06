// Lean compiler output
// Module: typeFormerPolymorphism
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn l_Std_Format_pretty(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_foo___redArg(mut v_f_1_: *mut lean_object, mut v_a_2_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); 
lean_inc_n(v_f_1_, 2);
lean_inc(v_a_2_);
v___x_3_ = lean_apply_1(v_f_1_, v_a_2_);
v___x_4_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_4_, 0, v_f_1_);
lean_ctor_set(v___x_4_, 1, v_f_1_);
v___x_5_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_5_, 0, v___x_3_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
v___x_6_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_6_, 0, v_a_2_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
return v___x_6_;
}
#[no_mangle] pub unsafe extern "C" fn l_foo(mut v_00_u03b1_7_: *mut lean_object, mut v_00_u03b2_8_: *mut lean_object, mut v_f_9_: *mut lean_object, mut v_a_10_: *mut lean_object) -> *mut lean_object{
let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = l_foo___redArg(v_f_9_, v_a_10_);
return v___x_11_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_12_: *mut lean_object) -> *mut lean_object{
let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_15_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); 
v___x_14_ = lean_get_stdout();
v_putStr_15_ = lean_ctor_get(v___x_14_, 4);
lean_inc_ref(v_putStr_15_);
lean_dec_ref(v___x_14_);
v___x_16_ = lean_apply_2(v_putStr_15_, v_s_12_, lean_box(0));
return v___x_16_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_17_: *mut lean_object, mut v_a_18_: *mut lean_object) -> *mut lean_object{
let mut v_res_19_: *mut lean_object = core::ptr::null_mut(); 
v_res_19_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_17_);
return v_res_19_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_20_: *mut lean_object) -> *mut lean_object{
let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: u32 = 0; let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); 
v___x_22_ = lean_unsigned_to_nat(120);
v___x_23_ = lean_unsigned_to_nat(0);
v___x_24_ = l_Std_Format_pretty(v_s_20_, v___x_22_, v___x_23_, v___x_23_);
v___x_25_ = 10;
v___x_26_ = lean_string_push(v___x_24_, v___x_25_);
v___x_27_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_26_);
return v___x_27_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_28_: *mut lean_object, mut v_a_29_: *mut lean_object) -> *mut lean_object{
let mut v_res_30_: *mut lean_object = core::ptr::null_mut(); 
v_res_30_ = l_IO_println___at___00main_spec__0(v_s_28_);
return v_res_30_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> *mut lean_object{
let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
v___x_31_ = lean_unsigned_to_nat(42);
v___x_32_ = l_foo___redArg(lean_box(0), v___x_31_);
return v___x_32_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); 
v___x_34_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v_fst_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_fst_35_);
v___x_36_ = l_Nat_reprFast(v_fst_35_);
v___x_37_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_37_, 0, v___x_36_);
v___x_38_ = l_IO_println___at___00main_spec__0(v___x_37_);
return v___x_38_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_39_: *mut lean_object) -> *mut lean_object{
let mut v_res_40_: *mut lean_object = core::ptr::null_mut(); 
v_res_40_ = _lean_main();
return v_res_40_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_typeFormerPolymorphism(builtin: u8) -> *mut lean_object {
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
  let res = initialize_typeFormerPolymorphism(1 /* builtin */);
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

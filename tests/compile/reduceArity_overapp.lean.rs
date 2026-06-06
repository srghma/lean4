// Lean compiler output
// Module: reduceArity_overapp
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_to_int(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_main___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object] };
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__4_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l_main___closed__4: *mut lean_object = core::ptr::addr_of!(l_main___closed__4_value) as *mut lean_object;
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_curry___redArg___lam__0(mut v___y_1_: *mut lean_object, mut v_f_2_: *mut lean_object, mut v_xs_3_: *mut lean_object) -> *mut lean_object{
let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_4_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_4_, 0, v___y_1_);
lean_ctor_set(v___x_4_, 1, v_xs_3_);
v___x_5_ = lean_apply_1(v_f_2_, v___x_4_);
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_curry___redArg___lam__2(mut v_tail_6_: *mut lean_object, mut v_f_7_: *mut lean_object, mut v___y_8_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_tail_6_) == 0 {
let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); 
v___x_9_ = lean_apply_1(v_f_7_, v___y_8_);
return v___x_9_;
} else {
let mut v_tail_10_: *mut lean_object = core::ptr::null_mut(); let mut v___f_11_: *mut lean_object = core::ptr::null_mut(); let mut v___f_12_: *mut lean_object = core::ptr::null_mut(); 
v_tail_10_ = lean_ctor_get(v_tail_6_, 1);
lean_inc(v_tail_10_);
lean_dec_ref_known(v_tail_6_, 2);
v___f_11_ = lean_alloc_closure(l_curry___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_11_, 0, v___y_8_);
lean_closure_set(v___f_11_, 1, v_f_7_);
v___f_12_ = lean_alloc_closure(l_curry___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_12_, 0, v_tail_10_);
lean_closure_set(v___f_12_, 1, v___f_11_);
return v___f_12_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_curry___redArg(mut v_ins_13_: *mut lean_object, mut v_f_14_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_ins_13_) == 0 {
let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); 
v___x_15_ = lean_box(0);
v___x_16_ = lean_apply_1(v_f_14_, v___x_15_);
return v___x_16_;
} else {
let mut v_tail_17_: *mut lean_object = core::ptr::null_mut(); let mut v___f_18_: *mut lean_object = core::ptr::null_mut(); 
v_tail_17_ = lean_ctor_get(v_ins_13_, 1);
lean_inc(v_tail_17_);
lean_dec_ref_known(v_ins_13_, 2);
v___f_18_ = lean_alloc_closure(l_curry___redArg___lam__2 as *mut core::ffi::c_void, 3, 2);
lean_closure_set(v___f_18_, 0, v_tail_17_);
lean_closure_set(v___f_18_, 1, v_f_14_);
return v___f_18_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_curry___redArg___lam__1(mut v_tail_19_: *mut lean_object, mut v___f_20_: *mut lean_object, mut v___y_21_: *mut lean_object) -> *mut lean_object{
let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_122__overap_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); 
v___x_22_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_22_, 0, lean_box(0));
lean_ctor_set(v___x_22_, 1, v_tail_19_);
v___x_122__overap_23_ = l_curry___redArg(v___x_22_, v___f_20_);
v___x_24_ = lean_apply_1(v___x_122__overap_23_, v___y_21_);
return v___x_24_;
}
#[no_mangle] pub unsafe extern "C" fn l_curry(mut v_ins_25_: *mut lean_object, mut v_out_26_: *mut lean_object, mut v_f_27_: *mut lean_object) -> *mut lean_object{
let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); 
v___x_28_ = l_curry___redArg(v_ins_25_, v_f_27_);
return v___x_28_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0(mut v_self_29_: *mut lean_object) -> *mut lean_object{
let mut v_snd_30_: *mut lean_object = core::ptr::null_mut(); 
v_snd_30_ = lean_ctor_get(v_self_29_, 1);
lean_inc(v_snd_30_);
return v_snd_30_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0___boxed(mut v_self_31_: *mut lean_object) -> *mut lean_object{
let mut v_res_32_: *mut lean_object = core::ptr::null_mut(); 
v_res_32_ = l_main___lam__0(v_self_31_);
lean_dec_ref(v_self_31_);
return v_res_32_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_33_: *mut lean_object) -> *mut lean_object{
let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); 
v___x_35_ = lean_get_stdout();
v_putStr_36_ = lean_ctor_get(v___x_35_, 4);
lean_inc_ref(v_putStr_36_);
lean_dec_ref(v___x_35_);
v___x_37_ = lean_apply_2(v_putStr_36_, v_s_33_, lean_box(0));
return v___x_37_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_38_: *mut lean_object, mut v_a_39_: *mut lean_object) -> *mut lean_object{
let mut v_res_40_: *mut lean_object = core::ptr::null_mut(); 
v_res_40_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_38_);
return v_res_40_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_41_: *mut lean_object) -> *mut lean_object{
let mut v___x_43_: u32 = 0; let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); 
v___x_43_ = 10;
v___x_44_ = lean_string_push(v_s_41_, v___x_43_);
v___x_45_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_44_);
return v___x_45_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_46_: *mut lean_object, mut v_a_47_: *mut lean_object) -> *mut lean_object{
let mut v_res_48_: *mut lean_object = core::ptr::null_mut(); 
v_res_48_ = l_IO_println___at___00main_spec__0(v_s_46_);
return v_res_48_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> *mut lean_object{
let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); 
v___x_54_ = lean_unsigned_to_nat(1);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___f_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v_val_overap_61_: *mut lean_object = core::ptr::null_mut(); let mut v_val_62_: *mut lean_object = core::ptr::null_mut(); 
v___x_57_ = l_main___closed__4;
v___x_58_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___f_59_ = l_main___closed__0;
v___x_60_ = l_main___closed__2;
v_val_overap_61_ = l_curry___redArg(v___x_60_, v___f_59_);
v_val_62_ = lean_apply_2(v_val_overap_61_, v___x_58_, v___x_57_);
return v_val_62_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v_val_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); 
v_val_64_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_65_ = l_IO_println___at___00main_spec__0(v_val_64_);
return v___x_65_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_66_: *mut lean_object) -> *mut lean_object{
let mut v_res_67_: *mut lean_object = core::ptr::null_mut(); 
v_res_67_ = _lean_main();
return v_res_67_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_reduceArity__overapp(builtin: u8) -> *mut lean_object {
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
  let res = initialize_reduceArity__overapp(1 /* builtin */);
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

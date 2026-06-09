// Lean compiler output
// Module: uset
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Data::UInt::BasicAux::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
pub static l_main___closed__0_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + core::mem::size_of::<usize>()*1 + 8) as u16, m_other: 1, m_tag: 0 }, m_objs: [(0 as *mut lean_object),0 as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_Point_right(mut v_p_1_: *mut lean_object) -> *mut lean_object{
let mut v_x_2_: usize = 0; let mut v_y_3_: u32 = 0; let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_6_: u8 = 0; let mut v___x_7_: usize = 0; let mut v___x_8_: usize = 0; let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_11_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_12_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_x_2_ = lean_ctor_get_usize(v_p_1_, 0);
v_y_3_ = lean_ctor_get_uint32(v_p_1_, (core::mem::size_of::<*mut lean_object>()*1) as u32);
v_isSharedCheck_12_ = (!lean_is_exclusive(v_p_1_)) as u8;
if v_isSharedCheck_12_ == 0 {
v___x_5_ = v_p_1_;
v_isShared_6_ = v_isSharedCheck_12_;
state = 1; continue;
} else {
lean_dec(v_p_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_12_;
state = 1; continue;
}
}
1 => {
v___x_7_ = 1usize;
v___x_8_ = lean_usize_add(v_x_2_, v___x_7_);
if v_isShared_6_ == 0 {
v___x_10_ = v___x_5_;
state = 2; continue;
} else {
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 0, (core::mem::size_of::<usize>()*1 + 4) as u32);
lean_ctor_set_uint32(v_reuseFailAlloc_11_, (core::mem::size_of::<*mut lean_object>()*1) as u32, v_y_3_);
v___x_10_ = v_reuseFailAlloc_11_;
state = 2; continue;
}
}
2 => {
lean_ctor_set_usize(v___x_10_, 0, v___x_8_);
return v___x_10_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_13_: *mut lean_object) -> *mut lean_object{
let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); 
v___x_15_ = lean_get_stdout();
v_putStr_16_ = lean_ctor_get(v___x_15_, 4);
lean_inc_ref(v_putStr_16_);
lean_dec_ref(v___x_15_);
v___x_17_ = lean_apply_2(v_putStr_16_, v_s_13_, lean_box(0));
return v___x_17_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_18_: *mut lean_object, mut v_a_19_: *mut lean_object) -> *mut lean_object{
let mut v_res_20_: *mut lean_object = core::ptr::null_mut(); 
v_res_20_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_18_);
return v_res_20_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_21_: usize) -> *mut lean_object{
let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: u32 = 0; let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); 
v___x_23_ = lean_usize_to_nat(v_s_21_);
v___x_24_ = l_Nat_reprFast(v___x_23_);
v___x_25_ = 10;
v___x_26_ = lean_string_push(v___x_24_, v___x_25_);
v___x_27_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_26_);
return v___x_27_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_28_: *mut lean_object, mut v_a_29_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_30_: usize = 0; let mut v_res_31_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_30_ = lean_unbox_usize(v_s_28_);
lean_dec(v_s_28_);
v_res_31_ = l_IO_println___at___00main_spec__0(v_s_boxed_30_);
return v_res_31_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); 
v___x_35_ = l_main___closed__0;
v___x_36_ = l_Point_right(v___x_35_);
return v___x_36_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v_x_39_: usize = 0; let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
v___x_38_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v_x_39_ = lean_ctor_get_usize(v___x_38_, 0);
v___x_40_ = l_IO_println___at___00main_spec__0(v_x_39_);
return v___x_40_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_41_: *mut lean_object) -> *mut lean_object{
let mut v_res_42_: *mut lean_object = core::ptr::null_mut(); 
v_res_42_ = _lean_main();
return v_res_42_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_uset(builtin: u8) -> *mut lean_object {
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
  let res = initialize_uset(1 /* builtin */);
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

// Lean compiler output
// Module: wait_dedicated
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::String::Bootstrap::*;
extern "C" {
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_io_as_task(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
pub static l_stuff___closed__0_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [72, 105, 32, 116, 104, 101, 114, 101, 0]};
static mut l_stuff___closed__0: *mut lean_object = core::ptr::addr_of!(l_stuff___closed__0_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_closure_object<0> = lean_closure_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 245 }, m_fun: l_main___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00stuff_spec__0_spec__0(mut v_s_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_get_stdout();
v_putStr_4_ = lean_ctor_get(v___x_3_, 4);
lean_inc_ref(v_putStr_4_);
lean_dec_ref(v___x_3_);
v___x_5_ = lean_apply_2(v_putStr_4_, v_s_1_, lean_box(0));
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00stuff_spec__0_spec__0___boxed(mut v_s_6_: *mut lean_object, mut v_a_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_IO_print___at___00IO_println___at___00stuff_spec__0_spec__0(v_s_6_);
return v_res_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00stuff_spec__0(mut v_s_9_: *mut lean_object) -> *mut lean_object{
let mut v___x_11_: u32 = 0; let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = 10;
v___x_12_ = lean_string_push(v_s_9_, v___x_11_);
v___x_13_ = l_IO_print___at___00IO_println___at___00stuff_spec__0_spec__0(v___x_12_);
return v___x_13_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00stuff_spec__0___boxed(mut v_s_14_: *mut lean_object, mut v_a_15_: *mut lean_object) -> *mut lean_object{
let mut v_res_16_: *mut lean_object = core::ptr::null_mut(); 
v_res_16_ = l_IO_println___at___00stuff_spec__0(v_s_14_);
return v_res_16_;
}
#[no_mangle] pub unsafe extern "C" fn l_stuff() -> *mut lean_object{
let mut v___x_19_: u32 = 0; let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); 
v___x_19_ = 100;
v___x_20_ = l_IO_sleep(v___x_19_);
v___x_21_ = l_stuff___closed__0;
v___x_22_ = l_IO_println___at___00stuff_spec__0(v___x_21_);
return v___x_22_;
}
#[no_mangle] pub unsafe extern "C" fn l_stuff___boxed(mut v_a_23_: *mut lean_object) -> *mut lean_object{
let mut v_res_24_: *mut lean_object = core::ptr::null_mut(); 
v_res_24_ = l_stuff();
return v_res_24_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0() -> *mut lean_object{
let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v_a_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_30_: u8 = 0; let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_33_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_34_: u8 = 0; let mut v_a_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_38_: u8 = 0; let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_41_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_42_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_26_ = l_stuff();
if lean_obj_tag(v___x_26_) == 0 {
v_a_27_ = lean_ctor_get(v___x_26_, 0);
v_isSharedCheck_34_ = (!lean_is_exclusive(v___x_26_)) as u8;
if v_isSharedCheck_34_ == 0 {
v___x_29_ = v___x_26_;
v_isShared_30_ = v_isSharedCheck_34_;
state = 1; continue;
} else {
lean_inc(v_a_27_);
lean_dec(v___x_26_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
state = 1; continue;
}
} else {
v_a_35_ = lean_ctor_get(v___x_26_, 0);
v_isSharedCheck_42_ = (!lean_is_exclusive(v___x_26_)) as u8;
if v_isSharedCheck_42_ == 0 {
v___x_37_ = v___x_26_;
v_isShared_38_ = v_isSharedCheck_42_;
state = 3; continue;
} else {
lean_inc(v_a_35_);
lean_dec(v___x_26_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
state = 3; continue;
}
}
}
1 => {
if v_isShared_30_ == 0 {
lean_ctor_set_tag(v___x_29_, 1);
v___x_32_ = v___x_29_;
state = 2; continue;
} else {
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_27_);
v___x_32_ = v_reuseFailAlloc_33_;
state = 2; continue;
}
}
2 => {
return v___x_32_;
}
3 => {
if v_isShared_38_ == 0 {
lean_ctor_set_tag(v___x_37_, 0);
v___x_40_ = v___x_37_;
state = 4; continue;
} else {
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_35_);
v___x_40_ = v_reuseFailAlloc_41_;
state = 4; continue;
}
}
4 => {
return v___x_40_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___lam__0___boxed(mut v___y_43_: *mut lean_object) -> *mut lean_object{
let mut v_res_44_: *mut lean_object = core::ptr::null_mut(); 
v_res_44_ = l_main___lam__0();
return v_res_44_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___f_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); 
v___f_47_ = l_main___closed__0;
v___x_48_ = lean_unsigned_to_nat(9);
v___x_49_ = lean_io_as_task(v___f_47_, v___x_48_);
lean_dec_ref(v___x_49_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_52_: *mut lean_object) -> *mut lean_object{
let mut v_res_53_: *mut lean_object = core::ptr::null_mut(); 
v_res_53_ = _lean_main();
return v_res_53_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_wait__dedicated(builtin: u8) -> *mut lean_object {
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
  let res = initialize_wait__dedicated(1 /* builtin */);
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

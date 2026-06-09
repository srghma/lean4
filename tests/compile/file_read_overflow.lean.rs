// Lean compiler output
// Module: file_read_overflow
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::UInt::BasicAux::*;
extern "C" {
    fn lean_io_create_tempfile() -> *mut lean_object;
    fn lean_io_prim_handle_read(_: *mut lean_object, _: usize) -> *mut lean_object;
}
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: usize = 0;
#[used]
#[no_mangle]
pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___boxed__const__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> usize{
let mut v___x_1_: usize = 0; let mut v___x_2_: usize = 0; let mut v___x_3_: usize = 0; 
v___x_1_ = 1usize;
v___x_2_ = 0usize;
v___x_3_ = lean_usize_sub(v___x_2_, v___x_1_);
return v___x_3_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_4_: u32 = 0; let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_4_ = 1;
v___x_5_ = lean_box_uint32(v___x_4_);
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__2() -> *mut lean_object{
let mut v___x_6_: u32 = 0; let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); 
v___x_6_ = 0;
v___x_7_ = lean_box_uint32(v___x_6_);
return v___x_7_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v_a_10_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: usize = 0; let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_16_: u8 = 0; let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_20_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_21_: u8 = 0; let mut v_unused_22_: *mut lean_object = core::ptr::null_mut(); let mut v_a_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_26_: u8 = 0; let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_30_: *mut lean_object = core::ptr::null_mut(); let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_34_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_35_: u8 = 0; let mut v_a_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_39_: u8 = 0; let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_42_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_43_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_9_ = lean_io_create_tempfile();
if lean_obj_tag(v___x_9_) == 0 {
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v___x_9_, 1);
v_fst_11_ = lean_ctor_get(v_a_10_, 0);
lean_inc(v_fst_11_);
lean_dec(v_a_10_);
v___x_12_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v___x_13_ = lean_io_prim_handle_read(v_fst_11_, v___x_12_);
lean_dec(v_fst_11_);
if lean_obj_tag(v___x_13_) == 0 {
v_isSharedCheck_21_ = (!lean_is_exclusive(v___x_13_)) as u8;
if v_isSharedCheck_21_ == 0 {
v_unused_22_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_22_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_21_;
state = 1; continue;
} else {
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_21_;
state = 1; continue;
}
} else {
v_a_23_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_35_ = (!lean_is_exclusive(v___x_13_)) as u8;
if v_isSharedCheck_35_ == 0 {
v___x_25_ = v___x_13_;
v_isShared_26_ = v_isSharedCheck_35_;
state = 3; continue;
} else {
lean_inc(v_a_23_);
lean_dec(v___x_13_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_35_;
state = 3; continue;
}
}
} else {
v_a_36_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_43_ = (!lean_is_exclusive(v___x_9_)) as u8;
if v_isSharedCheck_43_ == 0 {
v___x_38_ = v___x_9_;
v_isShared_39_ = v_isSharedCheck_43_;
state = 6; continue;
} else {
lean_inc(v_a_36_);
lean_dec(v___x_9_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
state = 6; continue;
}
}
}
1 => {
v___x_17_ = l_main___boxed__const__1;
if v_isShared_16_ == 0 {
lean_ctor_set(v___x_15_, 0, v___x_17_);
v___x_19_ = v___x_15_;
state = 2; continue;
} else {
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
state = 2; continue;
}
}
2 => {
return v___x_19_;
}
3 => {
if lean_obj_tag(v_a_23_) == 14 {
lean_dec_ref_known(v_a_23_, 2);
v___x_27_ = l_main___boxed__const__2;
if v_isShared_26_ == 0 {
lean_ctor_set_tag(v___x_25_, 0);
lean_ctor_set(v___x_25_, 0, v___x_27_);
v___x_29_ = v___x_25_;
state = 4; continue;
} else {
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
state = 4; continue;
}
} else {
lean_dec(v_a_23_);
v___x_31_ = l_main___boxed__const__1;
if v_isShared_26_ == 0 {
lean_ctor_set_tag(v___x_25_, 0);
lean_ctor_set(v___x_25_, 0, v___x_31_);
v___x_33_ = v___x_25_;
state = 5; continue;
} else {
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
state = 5; continue;
}
}
}
4 => {
return v___x_29_;
}
5 => {
return v___x_33_;
}
6 => {
if v_isShared_39_ == 0 {
v___x_41_ = v___x_38_;
state = 7; continue;
} else {
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
state = 7; continue;
}
}
7 => {
return v___x_41_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_44_: *mut lean_object) -> *mut lean_object{
let mut v_res_45_: *mut lean_object = core::ptr::null_mut(); 
v_res_45_ = _lean_main();
return v_res_45_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_file__read__overflow(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
l_main___boxed__const__2 = _init_l_main___boxed__const__2();
lean_mark_persistent(l_main___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_file__read__overflow(1 /* builtin */);
  lean_io_mark_end_initialization();
  let mut ret_val = 1;
  if lean_io_result_is_ok(res) {
    lean_dec(res);
    lean_init_task_manager();
    let main_res = lean_run_main(run_main, argc, argv);
    lean_finalize_task_manager();
    if lean_io_result_is_ok(main_res) {
      ret_val = lean_unbox_uint32(lean_io_result_get_value(main_res)) as i32;
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

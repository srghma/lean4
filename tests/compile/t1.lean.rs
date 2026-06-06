// Lean compiler output
// Module: t1
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[no_mangle] pub static l_main___redArg___closed__0_value: lean_string_object<12> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 0]};
static mut l_main___redArg___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___redArg___closed__0_value) as *mut lean_object;
#[no_mangle] pub static mut l_main___redArg___boxed__const__1: *mut lean_object = core::ptr::null_mut();
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
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___boxed__const__1() -> *mut lean_object{
let mut v___x_18_: u32 = 0; let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); 
v___x_18_ = 0;
v___x_19_ = lean_box_uint32(v___x_18_);
return v___x_19_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg() -> *mut lean_object{
let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_25_: u8 = 0; let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_29_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_30_: u8 = 0; let mut v_unused_31_: *mut lean_object = core::ptr::null_mut(); let mut v_a_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_35_: u8 = 0; let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_38_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_39_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_21_ = l_main___redArg___closed__0;
v___x_22_ = l_IO_println___at___00main_spec__0(v___x_21_);
if lean_obj_tag(v___x_22_) == 0 {
let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_25_: u8 = 0; let mut v_isSharedCheck_30_: u8 = 0; 
v_isSharedCheck_30_ = (!lean_is_exclusive(v___x_22_)) as u8;
if v_isSharedCheck_30_ == 0 {
let mut v_unused_31_: *mut lean_object = core::ptr::null_mut(); 
v_unused_31_ = lean_ctor_get(v___x_22_, 0);
lean_dec(v_unused_31_);
v___x_24_ = v___x_22_;
v_isShared_25_ = v_isSharedCheck_30_;
state = 1; continue;
} else {
lean_dec(v___x_22_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
state = 1; continue;
}
} else {
let mut v_a_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_35_: u8 = 0; let mut v_isSharedCheck_39_: u8 = 0; 
v_a_32_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_39_ = (!lean_is_exclusive(v___x_22_)) as u8;
if v_isSharedCheck_39_ == 0 {
v___x_34_ = v___x_22_;
v_isShared_35_ = v_isSharedCheck_39_;
state = 3; continue;
} else {
lean_inc(v_a_32_);
lean_dec(v___x_22_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
state = 3; continue;
}
}
}
1 => {
v___x_26_ = l_main___redArg___boxed__const__1;
if v_isShared_25_ == 0 {
lean_ctor_set(v___x_24_, 0, v___x_26_);
v___x_28_ = v___x_24_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_29_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
state = 2; continue;
}
}
3 => {
if v_isShared_35_ == 0 {
v___x_37_ = v___x_34_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_38_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___boxed(mut v_a_40_: *mut lean_object) -> *mut lean_object{
let mut v_res_41_: *mut lean_object = core::ptr::null_mut(); 
v_res_41_ = l_main___redArg();
return v_res_41_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_42_: *mut lean_object) -> *mut lean_object{
let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_xs_42_);
v___x_44_ = l_main___redArg();
return v___x_44_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_45_: *mut lean_object, mut v_a_46_: *mut lean_object) -> *mut lean_object{
let mut v_res_47_: *mut lean_object = core::ptr::null_mut(); 
v_res_47_ = _lean_main(v_xs_45_);
return v_res_47_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_t1(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_main___redArg___boxed__const__1 = _init_l_main___redArg___boxed__const__1();
lean_mark_persistent(l_main___redArg___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    let mut args_list = lean_box(0);
            let mut i = argc;
            while i > 1 {
                i -= 1;
                let arg_str = lean_mk_string(*argv.add(i as usize));
                let mut fields = [arg_str, args_list];
                args_list = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(args_list, 0, arg_str);
                lean_ctor_set(args_list, 1, fields[1]);
            }
            return _lean_main(args_list);
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_t1(1 /* builtin */);
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

// Lean compiler output
// Module: utf8Path
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    static mut l_instInhabitedError: *mut lean_object;
    fn l_instInhabitedEIO___aux__1___boxed(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_System_FilePath_pathExists(_: *mut lean_object) -> u8;
    fn l_mkPanicMessageWithDecl(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_panic_fn_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
static mut l_panic___at___00main_spec__0___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_panic___at___00main_spec__0___closed__0: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<21> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 21, m_capacity: 21, m_length: 16, m_data: [117, 116, 102, 56, 80, 97, 116, 104, 46, 108, 101, 97, 110, 46, 232, 139, 177, 232, 170, 158, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__1_value: lean_string_object<9> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [117, 116, 102, 56, 80, 97, 116, 104, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__2_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 97, 105, 110, 0]};
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__3_value: lean_string_object<75> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 117, 116, 102, 56, 80, 97, 116, 104, 46, 56, 54, 56, 56, 50, 57, 55, 53, 56, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 56, 46, 48, 32, 41, 10, 0]};
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn _init_l_panic___at___00main_spec__0___closed__0() -> *mut lean_object{
let mut v___x_1_: *mut lean_object = core::ptr::null_mut(); let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); 
v___x_1_ = l_instInhabitedError;
v___x_2_ = lean_alloc_closure(l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void, 4, 3);
lean_closure_set(v___x_2_, 0, lean_box(0));
lean_closure_set(v___x_2_, 1, lean_box(0));
lean_closure_set(v___x_2_, 2, v___x_1_);
return v___x_2_;
}
#[no_mangle] pub unsafe extern "C" fn l_panic___at___00main_spec__0(mut v_msg_3_: *mut lean_object) -> *mut lean_object{
let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190__overap_6_: *mut lean_object = core::ptr::null_mut(); let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); 
v___x_5_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00main_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00main_spec__0___closed__0_once), _init_l_panic___at___00main_spec__0___closed__0);
v___x_190__overap_6_ = lean_panic_fn_borrowed(v___x_5_, v_msg_3_);
v___x_7_ = lean_apply_1(v___x_190__overap_6_, lean_box(0));
return v___x_7_;
}
#[no_mangle] pub unsafe extern "C" fn l_panic___at___00main_spec__0___boxed(mut v_msg_8_: *mut lean_object, mut v___y_9_: *mut lean_object) -> *mut lean_object{
let mut v_res_10_: *mut lean_object = core::ptr::null_mut(); 
v_res_10_ = l_panic___at___00main_spec__0(v_msg_8_);
return v_res_10_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> *mut lean_object{
let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); 
v___x_15_ = l_main___closed__3;
v___x_16_ = lean_unsigned_to_nat(2);
v___x_17_ = lean_unsigned_to_nat(4);
v___x_18_ = l_main___closed__2;
v___x_19_ = l_main___closed__1;
v___x_20_ = l_mkPanicMessageWithDecl(v___x_19_, v___x_18_, v___x_17_, v___x_16_, v___x_15_);
return v___x_20_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: u8 = 0; 
v___x_22_ = l_main___closed__0;
v___x_23_ = l_System_FilePath_pathExists(v___x_22_);
if v___x_23_ == 0 {
let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); 
v___x_24_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___x_25_ = l_panic___at___00main_spec__0(v___x_24_);
return v___x_25_;
} else {
let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); 
v___x_26_ = lean_box(0);
v___x_27_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_28_: *mut lean_object) -> *mut lean_object{
let mut v_res_29_: *mut lean_object = core::ptr::null_mut(); 
v_res_29_ = _lean_main();
return v_res_29_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_utf8Path(builtin: u8) -> *mut lean_object {
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
  let res = initialize_utf8Path(1 /* builtin */);
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

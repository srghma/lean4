// Lean compiler output
// Module: append
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Data::List::Basic::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
static mut l_main___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__3: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__4: *mut lean_object = core::ptr::null_mut();
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
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__0() -> *mut lean_object{
let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v_ys1_19_: *mut lean_object = core::ptr::null_mut(); 
v___x_17_ = lean_unsigned_to_nat(1);
v___x_18_ = lean_unsigned_to_nat(1000000);
v_ys1_19_ = l_List_replicateTR___redArg(v___x_18_, v___x_17_);
return v_ys1_19_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__1() -> *mut lean_object{
let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v_ys2_22_: *mut lean_object = core::ptr::null_mut(); 
v___x_20_ = lean_unsigned_to_nat(2);
v___x_21_ = lean_unsigned_to_nat(1000000);
v_ys2_22_ = l_List_replicateTR___redArg(v___x_21_, v___x_20_);
return v_ys2_22_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__2() -> *mut lean_object{
let mut v_ys2_23_: *mut lean_object = core::ptr::null_mut(); let mut v_ys1_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); 
v_ys2_23_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__1), core::ptr::addr_of_mut!(l_main___redArg___closed__1_once), _init_l_main___redArg___closed__1);
v_ys1_24_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__0), core::ptr::addr_of_mut!(l_main___redArg___closed__0_once), _init_l_main___redArg___closed__0);
v___x_25_ = l_List_appendTR___redArg(v_ys1_24_, v_ys2_23_);
return v___x_25_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__3() -> *mut lean_object{
let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); 
v___x_26_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__2), core::ptr::addr_of_mut!(l_main___redArg___closed__2_once), _init_l_main___redArg___closed__2);
v___x_27_ = l_List_lengthTR___redArg(v___x_26_);
return v___x_27_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__4() -> *mut lean_object{
let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); 
v___x_28_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__3), core::ptr::addr_of_mut!(l_main___redArg___closed__3_once), _init_l_main___redArg___closed__3);
v___x_29_ = l_Nat_reprFast(v___x_28_);
return v___x_29_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg() -> *mut lean_object{
let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
v___x_31_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__4), core::ptr::addr_of_mut!(l_main___redArg___closed__4_once), _init_l_main___redArg___closed__4);
v___x_32_ = l_IO_println___at___00main_spec__0(v___x_31_);
return v___x_32_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___boxed(mut v_a_33_: *mut lean_object) -> *mut lean_object{
let mut v_res_34_: *mut lean_object = core::ptr::null_mut(); 
v_res_34_ = l_main___redArg();
return v_res_34_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_35_: *mut lean_object) -> *mut lean_object{
let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_xs_35_);
v___x_37_ = l_main___redArg();
return v___x_37_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_38_: *mut lean_object, mut v_a_39_: *mut lean_object) -> *mut lean_object{
let mut v_res_40_: *mut lean_object = core::ptr::null_mut(); 
v_res_40_ = _lean_main(v_xs_38_);
return v_res_40_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_append(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
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
  let res = initialize_append(1 /* builtin */);
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

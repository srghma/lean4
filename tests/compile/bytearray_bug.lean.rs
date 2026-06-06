// Lean compiler output
// Module: bytearray_bug
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    static mut l_ByteArray_empty: *mut lean_object;
    fn lean_byte_array_push(_: *mut lean_object, _: u8) -> *mut lean_object;
    fn lean_byte_array_data(_: *mut lean_object) -> *mut lean_object;
    static mut l_instInhabitedUInt8: u8;
    fn lean_array_get(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_uint8_to_nat(_: u8) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
static mut l_main___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__2: u8 = 0;
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
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_9_: u8) -> *mut lean_object{
let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: u32 = 0; let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = lean_uint8_to_nat(v_s_9_);
v___x_12_ = l_Nat_reprFast(v___x_11_);
v___x_13_ = 10;
v___x_14_ = lean_string_push(v___x_12_, v___x_13_);
v___x_15_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_14_);
return v___x_15_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_16_: *mut lean_object, mut v_a_17_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_18_: u8 = 0; let mut v_res_19_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_18_ = (lean_unbox(v_s_16_) as u8);
v_res_19_ = l_IO_println___at___00main_spec__0(v_s_boxed_18_);
return v_res_19_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__0() -> *mut lean_object{
let mut v___x_20_: u8 = 0; let mut v_e_21_: *mut lean_object = core::ptr::null_mut(); let mut v_arr_22_: *mut lean_object = core::ptr::null_mut(); 
v___x_20_ = 10;
v_e_21_ = l_ByteArray_empty;
v_arr_22_ = lean_byte_array_push(v_e_21_, v___x_20_);
return v_arr_22_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__1() -> *mut lean_object{
let mut v_arr_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); 
v_arr_23_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__0), core::ptr::addr_of_mut!(l_main___redArg___closed__0_once), _init_l_main___redArg___closed__0);
v___x_24_ = lean_byte_array_data(v_arr_23_);
return v___x_24_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__2() -> u8{
let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: u8 = 0; let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v_v_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_30_: u8 = 0; 
v___x_25_ = lean_unsigned_to_nat(0);
v___x_26_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__1), core::ptr::addr_of_mut!(l_main___redArg___closed__1_once), _init_l_main___redArg___closed__1);
v___x_27_ = l_instInhabitedUInt8;
v___x_28_ = lean_box((v___x_27_) as usize);
v_v_29_ = lean_array_get(v___x_28_, v___x_26_, v___x_25_);
lean_dec(v___x_28_);
v___x_30_ = (lean_unbox(v_v_29_) as u8);
lean_dec(v_v_29_);
return v___x_30_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg() -> *mut lean_object{
let mut v_v_32_: u8 = 0; let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); 
v_v_32_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___redArg___closed__2), core::ptr::addr_of_mut!(l_main___redArg___closed__2_once), _init_l_main___redArg___closed__2);
v___x_33_ = l_IO_println___at___00main_spec__0(v_v_32_);
return v___x_33_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___boxed(mut v_a_34_: *mut lean_object) -> *mut lean_object{
let mut v_res_35_: *mut lean_object = core::ptr::null_mut(); 
v_res_35_ = l_main___redArg();
return v_res_35_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_36_: *mut lean_object) -> *mut lean_object{
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_xs_36_);
v___x_38_ = l_main___redArg();
return v___x_38_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_39_: *mut lean_object, mut v_a_40_: *mut lean_object) -> *mut lean_object{
let mut v_res_41_: *mut lean_object = core::ptr::null_mut(); 
v_res_41_ = _lean_main(v_xs_39_);
return v_res_41_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_bytearray__bug(builtin: u8) -> *mut lean_object {
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
  let res = initialize_bytearray__bug(1 /* builtin */);
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

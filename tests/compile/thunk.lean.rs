// Lean compiler output
// Module: thunk
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn l_List_replicateTR___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_mk_thunk(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_thunk_get_own(_: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
static mut l_main___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___redArg___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___redArg___closed__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_main___redArg___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00compute_spec__0(mut v_x_1_: *mut lean_object, mut v_x_2_: *mut lean_object) -> *mut lean_object{
let mut v_head_3_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_2_) == 0 {
return v_x_1_;
} else {
let mut v_head_3_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v_head_3_ = lean_ctor_get(v_x_2_, 0);
v_tail_4_ = lean_ctor_get(v_x_2_, 1);
v___x_5_ = lean_nat_add(v_x_1_, v_head_3_);
lean_dec(v_x_1_);
v_x_1_ = v___x_5_;
v_x_2_ = v_tail_4_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00compute_spec__0___boxed(mut v_x_7_: *mut lean_object, mut v_x_8_: *mut lean_object) -> *mut lean_object{
let mut v_res_9_: *mut lean_object = core::ptr::null_mut(); 
v_res_9_ = l_List_foldl___at___00compute_spec__0(v_x_7_, v_x_8_);
lean_dec(v_x_8_);
return v_res_9_;
}
#[no_mangle] pub unsafe extern "C" fn l_compute___lam__0(mut v_v_10_: *mut lean_object, mut v_x_11_: *mut lean_object) -> *mut lean_object{
let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v_xs_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_12_ = lean_unsigned_to_nat(100000);
v_xs_13_ = l_List_replicateTR___redArg(v___x_12_, v_v_10_);
v___x_14_ = lean_unsigned_to_nat(0);
v___x_15_ = l_List_foldl___at___00compute_spec__0(v___x_14_, v_xs_13_);
lean_dec(v_xs_13_);
return v___x_15_;
}
#[no_mangle] pub unsafe extern "C" fn l_compute(mut v_v_16_: *mut lean_object) -> *mut lean_object{
let mut v___f_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); 
v___f_17_ = lean_alloc_closure(l_compute___lam__0 as *mut core::ffi::c_void, 2, 1);
lean_closure_set(v___f_17_, 0, v_v_16_);
v___x_18_ = lean_mk_thunk(v___f_17_);
return v___x_18_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00test_spec__0(mut v_t_19_: *mut lean_object, mut v_x_20_: *mut lean_object, mut v_x_21_: *mut lean_object) -> *mut lean_object{
let mut v_zero_22_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_23_: u8 = 0; let mut v_one_24_: *mut lean_object = core::ptr::null_mut(); let mut v_n_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_22_ = lean_unsigned_to_nat(0);
v_isZero_23_ = lean_nat_dec_eq(v_x_20_, v_zero_22_);
if v_isZero_23_ == 1 {
lean_dec(v_x_20_);
return v_x_21_;
} else {
let mut v_one_24_: *mut lean_object = core::ptr::null_mut(); let mut v_n_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); 
v_one_24_ = lean_unsigned_to_nat(1);
v_n_25_ = lean_nat_sub(v_x_20_, v_one_24_);
lean_dec(v_x_20_);
v___x_26_ = lean_thunk_get_own(v_t_19_);
v___x_27_ = lean_nat_add(v___x_26_, v_x_21_);
lean_dec(v_x_21_);
lean_dec(v___x_26_);
v_x_20_ = v_n_25_;
v_x_21_ = v___x_27_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00test_spec__0___boxed(mut v_t_29_: *mut lean_object, mut v_x_30_: *mut lean_object, mut v_x_31_: *mut lean_object) -> *mut lean_object{
let mut v_res_32_: *mut lean_object = core::ptr::null_mut(); 
v_res_32_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00test_spec__0(v_t_29_, v_x_30_, v_x_31_);
lean_dec_ref(v_t_29_);
return v_res_32_;
}
#[no_mangle] pub unsafe extern "C" fn l_test(mut v_t_33_: *mut lean_object, mut v_n_34_: *mut lean_object) -> *mut lean_object{
let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); 
v___x_35_ = lean_unsigned_to_nat(0);
v___x_36_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00test_spec__0(v_t_33_, v_n_34_, v___x_35_);
return v___x_36_;
}
#[no_mangle] pub unsafe extern "C" fn l_test___boxed(mut v_t_37_: *mut lean_object, mut v_n_38_: *mut lean_object) -> *mut lean_object{
let mut v_res_39_: *mut lean_object = core::ptr::null_mut(); 
v_res_39_ = l_test(v_t_37_, v_n_38_);
lean_dec_ref(v_t_37_);
return v_res_39_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_40_: *mut lean_object) -> *mut lean_object{
let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
v___x_42_ = lean_get_stdout();
v_putStr_43_ = lean_ctor_get(v___x_42_, 4);
lean_inc_ref(v_putStr_43_);
lean_dec_ref(v___x_42_);
v___x_44_ = lean_apply_2(v_putStr_43_, v_s_40_, lean_box(0));
return v___x_44_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_45_: *mut lean_object, mut v_a_46_: *mut lean_object) -> *mut lean_object{
let mut v_res_47_: *mut lean_object = core::ptr::null_mut(); 
v_res_47_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_45_);
return v_res_47_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_48_: *mut lean_object) -> *mut lean_object{
let mut v___x_50_: u32 = 0; let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); 
v___x_50_ = 10;
v___x_51_ = lean_string_push(v_s_48_, v___x_50_);
v___x_52_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_51_);
return v___x_52_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_53_: *mut lean_object, mut v_a_54_: *mut lean_object) -> *mut lean_object{
let mut v_res_55_: *mut lean_object = core::ptr::null_mut(); 
v_res_55_ = l_IO_println___at___00main_spec__0(v_s_53_);
return v_res_55_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__0() -> *mut lean_object{
let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); 
v___x_56_ = lean_unsigned_to_nat(1);
v___x_57_ = l_compute(v___x_56_);
return v___x_57_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__1() -> *mut lean_object{
let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); 
v___x_58_ = lean_unsigned_to_nat(100000);
v___x_59_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__0), core::ptr::addr_of_mut!(l_main___redArg___closed__0_once), _init_l_main___redArg___closed__0);
v___x_60_ = l_test(v___x_59_, v___x_58_);
return v___x_60_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___closed__2() -> *mut lean_object{
let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); 
v___x_61_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__1), core::ptr::addr_of_mut!(l_main___redArg___closed__1_once), _init_l_main___redArg___closed__1);
v___x_62_ = l_Nat_reprFast(v___x_61_);
return v___x_62_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___redArg___boxed__const__1() -> *mut lean_object{
let mut v___x_63_: u32 = 0; let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); 
v___x_63_ = 0;
v___x_64_ = lean_box_uint32(v___x_63_);
return v___x_64_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg() -> *mut lean_object{
let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_70_: u8 = 0; let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_74_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_75_: u8 = 0; let mut v_unused_76_: *mut lean_object = core::ptr::null_mut(); let mut v_a_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_80_: u8 = 0; let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_83_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_84_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_66_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___redArg___closed__2), core::ptr::addr_of_mut!(l_main___redArg___closed__2_once), _init_l_main___redArg___closed__2);
v___x_67_ = l_IO_println___at___00main_spec__0(v___x_66_);
if lean_obj_tag(v___x_67_) == 0 {
let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_70_: u8 = 0; let mut v_isSharedCheck_75_: u8 = 0; 
v_isSharedCheck_75_ = (!lean_is_exclusive(v___x_67_)) as u8;
if v_isSharedCheck_75_ == 0 {
let mut v_unused_76_: *mut lean_object = core::ptr::null_mut(); 
v_unused_76_ = lean_ctor_get(v___x_67_, 0);
lean_dec(v_unused_76_);
v___x_69_ = v___x_67_;
v_isShared_70_ = v_isSharedCheck_75_;
state = 1; continue;
} else {
lean_dec(v___x_67_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
state = 1; continue;
}
} else {
let mut v_a_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_80_: u8 = 0; let mut v_isSharedCheck_84_: u8 = 0; 
v_a_77_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_84_ = (!lean_is_exclusive(v___x_67_)) as u8;
if v_isSharedCheck_84_ == 0 {
v___x_79_ = v___x_67_;
v_isShared_80_ = v_isSharedCheck_84_;
state = 3; continue;
} else {
lean_inc(v_a_77_);
lean_dec(v___x_67_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
state = 3; continue;
}
}
}
1 => {
v___x_71_ = l_main___redArg___boxed__const__1;
if v_isShared_70_ == 0 {
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_74_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
state = 2; continue;
}
}
3 => {
if v_isShared_80_ == 0 {
v___x_82_ = v___x_79_;
state = 4; continue;
} else {
let mut v_reuseFailAlloc_83_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
state = 4; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___redArg___boxed(mut v_a_85_: *mut lean_object) -> *mut lean_object{
let mut v_res_86_: *mut lean_object = core::ptr::null_mut(); 
v_res_86_ = l_main___redArg();
return v_res_86_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_87_: *mut lean_object) -> *mut lean_object{
let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_xs_87_);
v___x_89_ = l_main___redArg();
return v___x_89_;
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_90_: *mut lean_object, mut v_a_91_: *mut lean_object) -> *mut lean_object{
let mut v_res_92_: *mut lean_object = core::ptr::null_mut(); 
v_res_92_ = _lean_main(v_xs_90_);
return v_res_92_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_thunk(builtin: u8) -> *mut lean_object {
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
  let res = initialize_thunk(1 /* builtin */);
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

// Lean compiler output
// Module: map_big
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
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_List_mapTR_loop___at___00f2_spec__0(mut v_ys_1_: *mut lean_object, mut v_a_2_: *mut lean_object, mut v_a_3_: *mut lean_object) -> *mut lean_object{
let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); let mut v_head_5_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_6_: *mut lean_object = core::ptr::null_mut(); let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_9_: u8 = 0; let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_14_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_15_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_a_2_) == 0 {
lean_dec(v_ys_1_);
v___x_4_ = l_List_reverse___redArg(v_a_3_);
return v___x_4_;
} else {
v_head_5_ = lean_ctor_get(v_a_2_, 0);
v_tail_6_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_15_ = (!lean_is_exclusive(v_a_2_)) as u8;
if v_isSharedCheck_15_ == 0 {
v___x_8_ = v_a_2_;
v_isShared_9_ = v_isSharedCheck_15_;
state = 1; continue;
} else {
lean_inc(v_tail_6_);
lean_inc(v_head_5_);
lean_dec(v_a_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_15_;
state = 1; continue;
}
}
}
1 => {
lean_inc(v_ys_1_);
if v_isShared_9_ == 0 {
lean_ctor_set(v___x_8_, 1, v_ys_1_);
v___x_11_ = v___x_8_;
state = 2; continue;
} else {
v_reuseFailAlloc_14_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_head_5_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_ys_1_);
v___x_11_ = v_reuseFailAlloc_14_;
state = 2; continue;
}
}
2 => {
v___x_12_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v_a_3_);
v_a_2_ = v_tail_6_;
v_a_3_ = v___x_12_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_f2(mut v_n_16_: *mut lean_object, mut v_xs_17_: *mut lean_object) -> *mut lean_object{
let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v_ys_19_: *mut lean_object = core::ptr::null_mut(); let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); 
v___x_18_ = lean_unsigned_to_nat(0);
v_ys_19_ = l_List_replicateTR___redArg(v_n_16_, v___x_18_);
v___x_20_ = lean_box(0);
v___x_21_ = l_List_mapTR_loop___at___00f2_spec__0(v_ys_19_, v_xs_17_, v___x_20_);
return v___x_21_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_22_: *mut lean_object) -> *mut lean_object{
let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); 
v___x_24_ = lean_get_stdout();
v_putStr_25_ = lean_ctor_get(v___x_24_, 4);
lean_inc_ref(v_putStr_25_);
lean_dec_ref(v___x_24_);
v___x_26_ = lean_apply_2(v_putStr_25_, v_s_22_, lean_box(0));
return v___x_26_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_27_: *mut lean_object, mut v_a_28_: *mut lean_object) -> *mut lean_object{
let mut v_res_29_: *mut lean_object = core::ptr::null_mut(); 
v_res_29_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_27_);
return v_res_29_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_30_: *mut lean_object) -> *mut lean_object{
let mut v___x_32_: u32 = 0; let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); 
v___x_32_ = 10;
v___x_33_ = lean_string_push(v_s_30_, v___x_32_);
v___x_34_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_33_);
return v___x_34_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_35_: *mut lean_object, mut v_a_36_: *mut lean_object) -> *mut lean_object{
let mut v_res_37_: *mut lean_object = core::ptr::null_mut(); 
v_res_37_ = l_IO_println___at___00main_spec__0(v_s_35_);
return v_res_37_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> *mut lean_object{
let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v_n_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); 
v___x_38_ = lean_unsigned_to_nat(0);
v_n_39_ = lean_unsigned_to_nat(100000);
v___x_40_ = l_List_replicateTR___redArg(v_n_39_, v___x_38_);
return v___x_40_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v_n_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); 
v___x_41_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v_n_42_ = lean_unsigned_to_nat(100000);
v___x_43_ = l_f2(v_n_42_, v___x_41_);
return v___x_43_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: *mut lean_object = core::ptr::null_mut(); 
v___x_44_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_45_ = l_List_lengthTR___redArg(v___x_44_);
return v___x_45_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> *mut lean_object{
let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); 
v___x_46_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_47_ = l_Nat_reprFast(v___x_46_);
return v___x_47_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_48_: u32 = 0; let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); 
v___x_48_ = 0;
v___x_49_ = lean_box_uint32(v___x_48_);
return v___x_49_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_55_: u8 = 0; let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_59_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_60_: u8 = 0; let mut v_unused_61_: *mut lean_object = core::ptr::null_mut(); let mut v_a_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_65_: u8 = 0; let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_68_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_69_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_51_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_52_ = l_IO_println___at___00main_spec__0(v___x_51_);
if lean_obj_tag(v___x_52_) == 0 {
v_isSharedCheck_60_ = (!lean_is_exclusive(v___x_52_)) as u8;
if v_isSharedCheck_60_ == 0 {
v_unused_61_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_61_);
v___x_54_ = v___x_52_;
v_isShared_55_ = v_isSharedCheck_60_;
state = 1; continue;
} else {
lean_dec(v___x_52_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_60_;
state = 1; continue;
}
} else {
v_a_62_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_69_ = (!lean_is_exclusive(v___x_52_)) as u8;
if v_isSharedCheck_69_ == 0 {
v___x_64_ = v___x_52_;
v_isShared_65_ = v_isSharedCheck_69_;
state = 3; continue;
} else {
lean_inc(v_a_62_);
lean_dec(v___x_52_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
state = 3; continue;
}
}
}
1 => {
v___x_56_ = l_main___boxed__const__1;
if v_isShared_55_ == 0 {
lean_ctor_set(v___x_54_, 0, v___x_56_);
v___x_58_ = v___x_54_;
state = 2; continue;
} else {
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
state = 2; continue;
}
}
2 => {
return v___x_58_;
}
3 => {
if v_isShared_65_ == 0 {
v___x_67_ = v___x_64_;
state = 4; continue;
} else {
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
state = 4; continue;
}
}
4 => {
return v___x_67_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_70_: *mut lean_object) -> *mut lean_object{
let mut v_res_71_: *mut lean_object = core::ptr::null_mut(); 
v_res_71_ = _lean_main();
return v_res_71_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_map__big(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_map__big(1 /* builtin */);
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

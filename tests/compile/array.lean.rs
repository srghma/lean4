// Lean compiler output
// Module: array
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::String::Defs::*;
extern "C" {
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_to_list(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_mk(_: *mut lean_object) -> *mut lean_object;
}
pub static l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3___closed__0_value) as *mut lean_object;
pub static l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__0_value) as *mut lean_object;
pub static l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1_value) as *mut lean_object;
pub static l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__2_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 4 as usize) << 1) | 1) as *mut lean_object,((( 0 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
pub static l_main___closed__1_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 3 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object] };
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
pub static l_main___closed__2_value: lean_ctor_object<2> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*2 + 0) as u16, m_other: 2, m_tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut lean_object,core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object] };
static mut l_main___closed__2: *mut lean_object = core::ptr::addr_of!(l_main___closed__2_value) as *mut lean_object;
pub static l_main___closed__3_value: lean_array_object<3> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*3) as u16, m_other: 0, m_tag: 246 }, m_size: 3, m_capacity: 3, m_data: [((( 2 as usize) << 1) | 1) as *mut lean_object,((( 3 as usize) << 1) | 1) as *mut lean_object,((( 4 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__6: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_f(mut v_a_1_: *mut lean_object) -> *mut lean_object{
let mut v_data_2_: *mut lean_object = core::ptr::null_mut(); let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); 
v_data_2_ = lean_array_to_list(v_a_1_);
v___x_3_ = l_List_lengthTR___redArg(v_data_2_);
lean_dec(v_data_2_);
return v___x_3_;
}
#[no_mangle] pub unsafe extern "C" fn l_g(mut v_a_4_: *mut lean_object) -> *mut lean_object{
let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_5_ = lean_array_to_list(v_a_4_);
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_h(mut v_a_6_: *mut lean_object) -> *mut lean_object{
let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); 
v___x_7_ = lean_array_mk(v_a_6_);
v___x_8_ = l_g(v___x_7_);
return v___x_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3(mut v_x_10_: *mut lean_object, mut v_x_11_: *mut lean_object) -> *mut lean_object{
let mut v_head_12_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_11_) == 0 {
return v_x_10_;
} else {
v_head_12_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_head_12_);
v_tail_13_ = lean_ctor_get(v_x_11_, 1);
lean_inc(v_tail_13_);
lean_dec_ref_known(v_x_11_, 2);
v___x_14_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3___closed__0;
v___x_15_ = lean_string_append(v_x_10_, v___x_14_);
v___x_16_ = l_Nat_reprFast(v_head_12_);
v___x_17_ = lean_string_append(v___x_15_, v___x_16_);
lean_dec_ref(v___x_16_);
v_x_10_ = v___x_17_;
v_x_11_ = v_tail_13_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00main_spec__1_spec__2(mut v_x_22_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_22_) == 0 {
let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); 
v___x_23_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__0;
return v___x_23_;
} else {
let mut v_tail_24_: *mut lean_object = core::ptr::null_mut(); 
v_tail_24_ = lean_ctor_get(v_x_22_, 1);
if lean_obj_tag(v_tail_24_) == 0 {
let mut v_head_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); 
v_head_25_ = lean_ctor_get(v_x_22_, 0);
lean_inc(v_head_25_);
lean_dec_ref_known(v_x_22_, 2);
v___x_26_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1;
v___x_27_ = l_Nat_reprFast(v_head_25_);
v___x_28_ = lean_string_append(v___x_26_, v___x_27_);
lean_dec_ref(v___x_27_);
v___x_29_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__2;
v___x_30_ = lean_string_append(v___x_28_, v___x_29_);
return v___x_30_;
} else {
let mut v_head_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: u32 = 0; let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_tail_24_);
v_head_31_ = lean_ctor_get(v_x_22_, 0);
lean_inc(v_head_31_);
lean_dec_ref_known(v_x_22_, 2);
v___x_32_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1;
v___x_33_ = l_Nat_reprFast(v_head_31_);
v___x_34_ = lean_string_append(v___x_32_, v___x_33_);
lean_dec_ref(v___x_33_);
v___x_35_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3(v___x_34_, v_tail_24_);
v___x_36_ = 93;
v___x_37_ = lean_string_push(v___x_35_, v___x_36_);
return v___x_37_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_38_: *mut lean_object) -> *mut lean_object{
let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); 
v___x_40_ = lean_get_stdout();
v_putStr_41_ = lean_ctor_get(v___x_40_, 4);
lean_inc_ref(v_putStr_41_);
lean_dec_ref(v___x_40_);
v___x_42_ = lean_apply_2(v_putStr_41_, v_s_38_, lean_box(0));
return v___x_42_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_43_: *mut lean_object, mut v_a_44_: *mut lean_object) -> *mut lean_object{
let mut v_res_45_: *mut lean_object = core::ptr::null_mut(); 
v_res_45_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_43_);
return v_res_45_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_46_: *mut lean_object) -> *mut lean_object{
let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: u32 = 0; let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); 
v___x_48_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2(v_s_46_);
v___x_49_ = 10;
v___x_50_ = lean_string_push(v___x_48_, v___x_49_);
v___x_51_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_50_);
return v___x_51_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_52_: *mut lean_object, mut v_a_53_: *mut lean_object) -> *mut lean_object{
let mut v_res_54_: *mut lean_object = core::ptr::null_mut(); 
v_res_54_ = l_IO_println___at___00main_spec__1(v_s_52_);
return v_res_54_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_55_: *mut lean_object) -> *mut lean_object{
let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: u32 = 0; let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); 
v___x_57_ = l_Nat_reprFast(v_s_55_);
v___x_58_ = 10;
v___x_59_ = lean_string_push(v___x_57_, v___x_58_);
v___x_60_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_59_);
return v___x_60_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_61_: *mut lean_object, mut v_a_62_: *mut lean_object) -> *mut lean_object{
let mut v_res_63_: *mut lean_object = core::ptr::null_mut(); 
v_res_63_ = l_IO_println___at___00main_spec__0(v_s_61_);
return v_res_63_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> *mut lean_object{
let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); 
v___x_80_ = l_main___closed__3;
v___x_81_ = l_f(v___x_80_);
return v___x_81_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); 
v___x_82_ = l_main___closed__3;
v___x_83_ = l_g(v___x_82_);
return v___x_83_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> *mut lean_object{
let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); 
v___x_84_ = l_main___closed__2;
v___x_85_ = l_h(v___x_84_);
return v___x_85_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); 
v___x_87_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___x_88_ = l_IO_println___at___00main_spec__0(v___x_87_);
if lean_obj_tag(v___x_88_) == 0 {
let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_88_, 1);
v___x_89_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_90_ = l_IO_println___at___00main_spec__1(v___x_89_);
if lean_obj_tag(v___x_90_) == 0 {
let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_90_, 1);
v___x_91_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v___x_92_ = l_IO_println___at___00main_spec__1(v___x_91_);
return v___x_92_;
} else {
return v___x_90_;
}
} else {
return v___x_88_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_93_: *mut lean_object) -> *mut lean_object{
let mut v_res_94_: *mut lean_object = core::ptr::null_mut(); 
v_res_94_ = _lean_main();
return v_res_94_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_array(builtin: u8) -> *mut lean_object {
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
  let res = initialize_array(1 /* builtin */);
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

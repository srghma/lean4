// Lean compiler output
// Module: nat_shiftr
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_get_stdout() -> *mut lean_object;
    fn l_Std_Format_pretty(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_usize_dec_lt(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_nat_shiftr(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_size(_: *mut lean_object) -> usize;
}
#[no_mangle] pub static l_test___closed__0_value: lean_array_object<12> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*12) as u16, m_other: 0, m_tag: 246 }, m_size: 12, m_capacity: 12, m_data: [((( 0 as usize) << 1) | 1) as *mut lean_object,((( 1 as usize) << 1) | 1) as *mut lean_object,((( 14 as usize) << 1) | 1) as *mut lean_object,((( 15 as usize) << 1) | 1) as *mut lean_object,((( 16 as usize) << 1) | 1) as *mut lean_object,((( 17 as usize) << 1) | 1) as *mut lean_object,((( 31 as usize) << 1) | 1) as *mut lean_object,((( 32 as usize) << 1) | 1) as *mut lean_object,((( 33 as usize) << 1) | 1) as *mut lean_object,((( 63 as usize) << 1) | 1) as *mut lean_object,((( 64 as usize) << 1) | 1) as *mut lean_object,((( 65 as usize) << 1) | 1) as *mut lean_object] };
static mut l_test___closed__0: *mut lean_object = core::ptr::addr_of!(l_test___closed__0_value) as *mut lean_object;
static mut l_test___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_test___closed__1: usize = 0;
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00test_spec__0_spec__0(mut v_s_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_get_stdout();
v_putStr_4_ = lean_ctor_get(v___x_3_, 4);
lean_inc_ref(v_putStr_4_);
lean_dec_ref(v___x_3_);
v___x_5_ = lean_apply_2(v_putStr_4_, v_s_1_, lean_box(0));
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00test_spec__0_spec__0___boxed(mut v_s_6_: *mut lean_object, mut v_a_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_IO_print___at___00IO_println___at___00test_spec__0_spec__0(v_s_6_);
return v_res_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00test_spec__0(mut v_s_9_: *mut lean_object) -> *mut lean_object{
let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: u32 = 0; let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v___x_16_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = lean_unsigned_to_nat(120);
v___x_12_ = lean_unsigned_to_nat(0);
v___x_13_ = l_Std_Format_pretty(v_s_9_, v___x_11_, v___x_12_, v___x_12_);
v___x_14_ = 10;
v___x_15_ = lean_string_push(v___x_13_, v___x_14_);
v___x_16_ = l_IO_print___at___00IO_println___at___00test_spec__0_spec__0(v___x_15_);
return v___x_16_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00test_spec__0___boxed(mut v_s_17_: *mut lean_object, mut v_a_18_: *mut lean_object) -> *mut lean_object{
let mut v_res_19_: *mut lean_object = core::ptr::null_mut(); 
v_res_19_ = l_IO_println___at___00test_spec__0(v_s_17_);
return v_res_19_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00test_spec__1(mut v_a_20_: *mut lean_object, mut v_as_21_: *mut lean_object, mut v_sz_22_: usize, mut v_i_23_: usize, mut v_b_24_: *mut lean_object) -> *mut lean_object{
let mut v___x_26_: u8 = 0; let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v_a_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: usize = 0; let mut v___x_35_: usize = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_26_ = lean_usize_dec_lt(v_i_23_, v_sz_22_);
if v___x_26_ == 0 {
let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); 
v___x_27_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_27_, 0, v_b_24_);
return v___x_27_;
} else {
let mut v_a_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
v_a_28_ = lean_array_uget_borrowed(v_as_21_, v_i_23_);
v___x_29_ = lean_nat_shiftr(v_a_20_, v_a_28_);
v___x_30_ = l_Nat_reprFast(v___x_29_);
v___x_31_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_31_, 0, v___x_30_);
v___x_32_ = l_IO_println___at___00test_spec__0(v___x_31_);
if lean_obj_tag(v___x_32_) == 0 {
let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: usize = 0; let mut v___x_35_: usize = 0; 
lean_dec_ref_known(v___x_32_, 1);
v___x_33_ = lean_box(0);
v___x_34_ = 1usize;
v___x_35_ = lean_usize_add(v_i_23_, v___x_34_);
v_i_23_ = v___x_35_;
v_b_24_ = v___x_33_;
state = 0; continue;
} else {
return v___x_32_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00test_spec__1___boxed(mut v_a_37_: *mut lean_object, mut v_as_38_: *mut lean_object, mut v_sz_39_: *mut lean_object, mut v_i_40_: *mut lean_object, mut v_b_41_: *mut lean_object, mut v___y_42_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_43_: usize = 0; let mut v_i_boxed_44_: usize = 0; let mut v_res_45_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_43_ = lean_unbox_usize(v_sz_39_);
lean_dec(v_sz_39_);
v_i_boxed_44_ = lean_unbox_usize(v_i_40_);
lean_dec(v_i_40_);
v_res_45_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00test_spec__1(v_a_37_, v_as_38_, v_sz_boxed_43_, v_i_boxed_44_, v_b_41_);
lean_dec_ref(v_as_38_);
lean_dec(v_a_37_);
return v_res_45_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_test___closed__1() -> usize{
let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_73_: usize = 0; 
v___x_72_ = l_test___closed__0;
v_sz_73_ = lean_array_size(v___x_72_);
return v_sz_73_;
}
#[no_mangle] pub unsafe extern "C" fn l_test(mut v_a_74_: *mut lean_object) -> *mut lean_object{
let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_78_: usize = 0; let mut v___x_79_: usize = 0; let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_83_: u8 = 0; let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_86_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_87_: u8 = 0; let mut v_unused_88_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_76_ = l_test___closed__0;
v___x_77_ = lean_box(0);
v_sz_78_ = lean_usize_once(core::ptr::addr_of_mut!(l_test___closed__1), core::ptr::addr_of_mut!(l_test___closed__1_once), _init_l_test___closed__1);
v___x_79_ = 0usize;
v___x_80_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00test_spec__1(v_a_74_, v___x_76_, v_sz_78_, v___x_79_, v___x_77_);
if lean_obj_tag(v___x_80_) == 0 {
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_83_: u8 = 0; let mut v_isSharedCheck_87_: u8 = 0; 
v_isSharedCheck_87_ = (!lean_is_exclusive(v___x_80_)) as u8;
if v_isSharedCheck_87_ == 0 {
let mut v_unused_88_: *mut lean_object = core::ptr::null_mut(); 
v_unused_88_ = lean_ctor_get(v___x_80_, 0);
lean_dec(v_unused_88_);
v___x_82_ = v___x_80_;
v_isShared_83_ = v_isSharedCheck_87_;
state = 1; continue;
} else {
lean_dec(v___x_80_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
state = 1; continue;
}
} else {
return v___x_80_;
}
}
1 => {
if v_isShared_83_ == 0 {
lean_ctor_set(v___x_82_, 0, v___x_77_);
v___x_85_ = v___x_82_;
state = 2; continue;
} else {
let mut v_reuseFailAlloc_86_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_77_);
v___x_85_ = v_reuseFailAlloc_86_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_test___boxed(mut v_a_89_: *mut lean_object, mut v_a_90_: *mut lean_object) -> *mut lean_object{
let mut v_res_91_: *mut lean_object = core::ptr::null_mut(); 
v_res_91_ = l_test(v_a_89_);
lean_dec(v_a_89_);
return v_res_91_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> *mut lean_object{
let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); 
v___x_92_ = lean_cstr_to_nat(b"18446744073709551615\0".as_ptr().cast());
return v___x_92_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); 
v___x_93_ = lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
return v___x_93_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); 
v___x_94_ = lean_cstr_to_nat(b"18446744073709551617\0".as_ptr().cast());
return v___x_94_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); 
v___x_96_ = lean_unsigned_to_nat(0);
v___x_97_ = l_test(v___x_96_);
if lean_obj_tag(v___x_97_) == 0 {
let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_97_, 1);
v___x_98_ = lean_unsigned_to_nat(1);
v___x_99_ = l_test(v___x_98_);
if lean_obj_tag(v___x_99_) == 0 {
let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_99_, 1);
v___x_100_ = lean_unsigned_to_nat(255);
v___x_101_ = l_test(v___x_100_);
if lean_obj_tag(v___x_101_) == 0 {
let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_101_, 1);
v___x_102_ = lean_unsigned_to_nat(256);
v___x_103_ = l_test(v___x_102_);
if lean_obj_tag(v___x_103_) == 0 {
let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_103_, 1);
v___x_104_ = lean_unsigned_to_nat(257);
v___x_105_ = l_test(v___x_104_);
if lean_obj_tag(v___x_105_) == 0 {
let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_105_, 1);
v___x_106_ = lean_unsigned_to_nat(65535);
v___x_107_ = l_test(v___x_106_);
if lean_obj_tag(v___x_107_) == 0 {
let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_107_, 1);
v___x_108_ = lean_unsigned_to_nat(65536);
v___x_109_ = l_test(v___x_108_);
if lean_obj_tag(v___x_109_) == 0 {
let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_109_, 1);
v___x_110_ = lean_unsigned_to_nat(65537);
v___x_111_ = l_test(v___x_110_);
if lean_obj_tag(v___x_111_) == 0 {
let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_111_, 1);
v___x_112_ = lean_unsigned_to_nat(4294967295);
v___x_113_ = l_test(v___x_112_);
if lean_obj_tag(v___x_113_) == 0 {
let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_113_, 1);
v___x_114_ = lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
v___x_115_ = l_test(v___x_114_);
if lean_obj_tag(v___x_115_) == 0 {
let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_115_, 1);
v___x_116_ = lean_cstr_to_nat(b"4294967297\0".as_ptr().cast());
v___x_117_ = l_test(v___x_116_);
if lean_obj_tag(v___x_117_) == 0 {
let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_117_, 1);
v___x_118_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v___x_119_ = l_test(v___x_118_);
if lean_obj_tag(v___x_119_) == 0 {
let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_119_, 1);
v___x_120_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_121_ = l_test(v___x_120_);
if lean_obj_tag(v___x_121_) == 0 {
let mut v___x_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_121_, 1);
v___x_122_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_123_ = l_test(v___x_122_);
return v___x_123_;
} else {
return v___x_121_;
}
} else {
return v___x_119_;
}
} else {
return v___x_117_;
}
} else {
return v___x_115_;
}
} else {
return v___x_113_;
}
} else {
return v___x_111_;
}
} else {
return v___x_109_;
}
} else {
return v___x_107_;
}
} else {
return v___x_105_;
}
} else {
return v___x_103_;
}
} else {
return v___x_101_;
}
} else {
return v___x_99_;
}
} else {
return v___x_97_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_124_: *mut lean_object) -> *mut lean_object{
let mut v_res_125_: *mut lean_object = core::ptr::null_mut(); 
v_res_125_ = _lean_main();
return v_res_125_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_nat__shiftr(builtin: u8) -> *mut lean_object {
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
  let res = initialize_nat__shiftr(1 /* builtin */);
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

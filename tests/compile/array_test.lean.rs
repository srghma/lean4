// Lean compiler output
// Module: array_test
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_size(_: *mut lean_object) -> usize;
    fn lean_usize_dec_lt(_: usize, _: usize) -> u8;
    fn lean_array_uget(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_array_uset(_: *mut lean_object, _: usize, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_to_list(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_usize_dec_eq(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_array_pop(_: *mut lean_object) -> *mut lean_object;
    fn lean_usize_of_nat(_: *mut lean_object) -> usize;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn l_Array_reverse___redArg(_: *mut lean_object) -> *mut lean_object;
    fn l_Array_extract___redArg(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
}
#[no_mangle] pub static l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__6_spec__8_spec__9___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__6_spec__8_spec__9___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__6_spec__8_spec__9___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_IO_println___at___00main_spec__6___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [35, 0]};
static mut l_IO_println___at___00main_spec__6___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__6___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__7: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__8: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__9: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__10: usize = 0;
static mut l_main___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__11: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__12_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__12: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__13: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__14_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__14: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__15_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__15: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__16_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__16: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__17_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__17: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__18_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__18: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__19_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__19: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__20_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__20: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__21_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__21: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__22_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__22: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__23_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__23: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__24_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__24: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__25_value: lean_array_object<4> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*4) as u16, m_other: 0, m_tag: 246 }, m_size: 4, m_capacity: 4, m_data: [((( 1 as usize) << 1) | 1) as *mut lean_object,((( 2 as usize) << 1) | 1) as *mut lean_object,((( 3 as usize) << 1) | 1) as *mut lean_object,((( 4 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__25: *mut lean_object = core::ptr::addr_of!(l_main___closed__25_value) as *mut lean_object;
static mut l_main___closed__26_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__26: usize = 0;
static mut l_main___closed__27_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__27: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__28_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__28: usize = 0;
static mut l_main___closed__29_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__29: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__30_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__30: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__31_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__31: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__32_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__32: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__33_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__33: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__34_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__34: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__35_value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_main___closed__35: *mut lean_object = core::ptr::addr_of!(l_main___closed__35_value) as *mut lean_object;
static mut l_main___closed__36_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__36: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__37_value: lean_array_object<3> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*3) as u16, m_other: 0, m_tag: 246 }, m_size: 3, m_capacity: 3, m_data: [((( 1 as usize) << 1) | 1) as *mut lean_object,((( 2 as usize) << 1) | 1) as *mut lean_object,((( 3 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__37: *mut lean_object = core::ptr::addr_of!(l_main___closed__37_value) as *mut lean_object;
static mut l_main___closed__38_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__38: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__39_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__39: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__40_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__40: u8 = 0;
static mut l_main___closed__41_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__41: u8 = 0;
static mut l_main___closed__42_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__42: usize = 0;
static mut l_main___closed__43_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__43: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__44_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__44: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__45_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__45: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__46_value: lean_array_object<5> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*5) as u16, m_other: 0, m_tag: 246 }, m_size: 5, m_capacity: 5, m_data: [((( 1 as usize) << 1) | 1) as *mut lean_object,((( 2 as usize) << 1) | 1) as *mut lean_object,((( 3 as usize) << 1) | 1) as *mut lean_object,((( 4 as usize) << 1) | 1) as *mut lean_object,((( 5 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__46: *mut lean_object = core::ptr::addr_of!(l_main___closed__46_value) as *mut lean_object;
static mut l_main___closed__47_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__47: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__48_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__48: u8 = 0;
static mut l_main___closed__49_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__49: u8 = 0;
static mut l_main___closed__50_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__50: usize = 0;
static mut l_main___closed__51_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__51: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__52_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__52: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_foo(mut v_a_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); let mut v_a_3_: *mut lean_object = core::ptr::null_mut(); let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); let mut v_a_5_: *mut lean_object = core::ptr::null_mut(); let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); let mut v_a_7_: *mut lean_object = core::ptr::null_mut(); let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); let mut v_a_9_: *mut lean_object = core::ptr::null_mut(); 
v___x_2_ = lean_unsigned_to_nat(0);
v_a_3_ = lean_array_push(v_a_1_, v___x_2_);
v___x_4_ = lean_unsigned_to_nat(1);
v_a_5_ = lean_array_push(v_a_3_, v___x_4_);
v___x_6_ = lean_unsigned_to_nat(2);
v_a_7_ = lean_array_push(v_a_5_, v___x_6_);
v___x_8_ = lean_unsigned_to_nat(3);
v_a_9_ = lean_array_push(v_a_7_, v___x_8_);
return v_a_9_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(mut v_sz_10_: usize, mut v_i_11_: usize, mut v_bs_12_: *mut lean_object) -> *mut lean_object{
let mut v___x_13_: u8 = 0; let mut v_v_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v_bs_x27_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: usize = 0; let mut v___x_20_: usize = 0; let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_13_ = lean_usize_dec_lt(v_i_11_, v_sz_10_);
if v___x_13_ == 0 {
return v_bs_12_;
} else {
let mut v_v_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); let mut v_bs_x27_16_: *mut lean_object = core::ptr::null_mut(); let mut v___x_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: usize = 0; let mut v___x_20_: usize = 0; let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); 
v_v_14_ = lean_array_uget(v_bs_12_, v_i_11_);
v___x_15_ = lean_unsigned_to_nat(0);
v_bs_x27_16_ = lean_array_uset(v_bs_12_, v_i_11_, v___x_15_);
v___x_17_ = lean_unsigned_to_nat(2);
v___x_18_ = lean_nat_add(v_v_14_, v___x_17_);
lean_dec(v_v_14_);
v___x_19_ = 1usize;
v___x_20_ = lean_usize_add(v_i_11_, v___x_19_);
v___x_21_ = lean_array_uset(v_bs_x27_16_, v_i_11_, v___x_18_);
v_i_11_ = v___x_20_;
v_bs_12_ = v___x_21_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4___boxed(mut v_sz_23_: *mut lean_object, mut v_i_24_: *mut lean_object, mut v_bs_25_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_26_: usize = 0; let mut v_i_boxed_27_: usize = 0; let mut v_res_28_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_26_ = lean_unbox_usize(v_sz_23_);
lean_dec(v_sz_23_);
v_i_boxed_27_ = lean_unbox_usize(v_i_24_);
lean_dec(v_i_24_);
v_res_28_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(v_sz_boxed_26_, v_i_boxed_27_, v_bs_25_);
return v_res_28_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__11_spec__14(mut v_as_29_: *mut lean_object, mut v_i_30_: usize, mut v_stop_31_: usize, mut v_b_32_: *mut lean_object) -> *mut lean_object{
let mut v___y_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: usize = 0; let mut v___x_36_: usize = 0; let mut v___x_38_: u8 = 0; let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: u8 = 0; let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_38_ = lean_usize_dec_eq(v_i_30_, v_stop_31_);
if v___x_38_ == 0 {
let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); let mut v___x_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: u8 = 0; 
v___x_39_ = lean_unsigned_to_nat(2);
v___x_40_ = lean_unsigned_to_nat(0);
v___x_41_ = lean_array_uget_borrowed(v_as_29_, v_i_30_);
v___x_42_ = lean_nat_mod(v___x_41_, v___x_39_);
v___x_43_ = lean_nat_dec_eq(v___x_42_, v___x_40_);
lean_dec(v___x_42_);
if v___x_43_ == 0 {
v___y_34_ = v_b_32_;
state = 1; continue;
} else {
let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v___x_41_);
v___x_44_ = lean_array_push(v_b_32_, v___x_41_);
v___y_34_ = v___x_44_;
state = 1; continue;
}
} else {
return v_b_32_;
}
}
1 => {
v___x_35_ = 1usize;
v___x_36_ = lean_usize_add(v_i_30_, v___x_35_);
v_i_30_ = v___x_36_;
v_b_32_ = v___y_34_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__11_spec__14___boxed(mut v_as_45_: *mut lean_object, mut v_i_46_: *mut lean_object, mut v_stop_47_: *mut lean_object, mut v_b_48_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_49_: usize = 0; let mut v_stop_boxed_50_: usize = 0; let mut v_res_51_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_49_ = lean_unbox_usize(v_i_46_);
lean_dec(v_i_46_);
v_stop_boxed_50_ = lean_unbox_usize(v_stop_47_);
lean_dec(v_stop_47_);
v_res_51_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__11_spec__14(v_as_45_, v_i_boxed_49_, v_stop_boxed_50_, v_b_48_);
lean_dec_ref(v_as_45_);
return v_res_51_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__11(mut v_as_52_: *mut lean_object, mut v_i_53_: usize, mut v_stop_54_: usize, mut v_b_55_: *mut lean_object) -> *mut lean_object{
let mut v___y_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: usize = 0; let mut v___x_59_: usize = 0; let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: u8 = 0; let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: u8 = 0; let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_61_ = lean_usize_dec_eq(v_i_53_, v_stop_54_);
if v___x_61_ == 0 {
let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: u8 = 0; 
v___x_62_ = lean_unsigned_to_nat(2);
v___x_63_ = lean_unsigned_to_nat(0);
v___x_64_ = lean_array_uget_borrowed(v_as_52_, v_i_53_);
v___x_65_ = lean_nat_mod(v___x_64_, v___x_62_);
v___x_66_ = lean_nat_dec_eq(v___x_65_, v___x_63_);
lean_dec(v___x_65_);
if v___x_66_ == 0 {
v___y_57_ = v_b_55_;
state = 1; continue;
} else {
let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v___x_64_);
v___x_67_ = lean_array_push(v_b_55_, v___x_64_);
v___y_57_ = v___x_67_;
state = 1; continue;
}
} else {
return v_b_55_;
}
}
1 => {
v___x_58_ = 1usize;
v___x_59_ = lean_usize_add(v_i_53_, v___x_58_);
v___x_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__11_spec__14(v_as_52_, v___x_59_, v_stop_54_, v___y_57_);
return v___x_60_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__11___boxed(mut v_as_68_: *mut lean_object, mut v_i_69_: *mut lean_object, mut v_stop_70_: *mut lean_object, mut v_b_71_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_72_: usize = 0; let mut v_stop_boxed_73_: usize = 0; let mut v_res_74_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_72_ = lean_unbox_usize(v_i_69_);
lean_dec(v_i_69_);
v_stop_boxed_73_ = lean_unbox_usize(v_stop_70_);
lean_dec(v_stop_70_);
v_res_74_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__11(v_as_68_, v_i_boxed_72_, v_stop_boxed_73_, v_b_71_);
lean_dec_ref(v_as_68_);
return v_res_74_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__9(mut v_as_75_: *mut lean_object, mut v_i_76_: usize, mut v_stop_77_: usize, mut v_b_78_: *mut lean_object) -> *mut lean_object{
let mut v___y_80_: *mut lean_object = core::ptr::null_mut(); let mut v___x_81_: usize = 0; let mut v___x_82_: usize = 0; let mut v___x_84_: u8 = 0; let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: u8 = 0; let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_84_ = lean_usize_dec_eq(v_i_76_, v_stop_77_);
if v___x_84_ == 0 {
let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: u8 = 0; 
v___x_85_ = lean_unsigned_to_nat(2);
v___x_86_ = lean_array_uget_borrowed(v_as_75_, v_i_76_);
v___x_87_ = lean_nat_dec_lt(v___x_85_, v___x_86_);
if v___x_87_ == 0 {
v___y_80_ = v_b_78_;
state = 1; continue;
} else {
let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v___x_86_);
v___x_88_ = lean_array_push(v_b_78_, v___x_86_);
v___y_80_ = v___x_88_;
state = 1; continue;
}
} else {
return v_b_78_;
}
}
1 => {
v___x_81_ = 1usize;
v___x_82_ = lean_usize_add(v_i_76_, v___x_81_);
v_i_76_ = v___x_82_;
v_b_78_ = v___y_80_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__9___boxed(mut v_as_89_: *mut lean_object, mut v_i_90_: *mut lean_object, mut v_stop_91_: *mut lean_object, mut v_b_92_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_93_: usize = 0; let mut v_stop_boxed_94_: usize = 0; let mut v_res_95_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_93_ = lean_unbox_usize(v_i_90_);
lean_dec(v_i_90_);
v_stop_boxed_94_ = lean_unbox_usize(v_stop_91_);
lean_dec(v_stop_91_);
v_res_95_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__9(v_as_89_, v_i_boxed_93_, v_stop_boxed_94_, v_b_92_);
lean_dec_ref(v_as_89_);
return v_res_95_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__10(mut v_as_96_: *mut lean_object, mut v_i_97_: usize, mut v_stop_98_: usize, mut v_b_99_: *mut lean_object) -> *mut lean_object{
let mut v___y_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: usize = 0; let mut v___x_103_: usize = 0; let mut v___x_105_: u8 = 0; let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: u8 = 0; let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_105_ = lean_usize_dec_eq(v_i_97_, v_stop_98_);
if v___x_105_ == 0 {
let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: u8 = 0; 
v___x_106_ = lean_unsigned_to_nat(2);
v___x_107_ = lean_unsigned_to_nat(1);
v___x_108_ = lean_array_uget_borrowed(v_as_96_, v_i_97_);
v___x_109_ = lean_nat_mod(v___x_108_, v___x_106_);
v___x_110_ = lean_nat_dec_eq(v___x_109_, v___x_107_);
lean_dec(v___x_109_);
if v___x_110_ == 0 {
v___y_101_ = v_b_99_;
state = 1; continue;
} else {
let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v___x_108_);
v___x_111_ = lean_array_push(v_b_99_, v___x_108_);
v___y_101_ = v___x_111_;
state = 1; continue;
}
} else {
return v_b_99_;
}
}
1 => {
v___x_102_ = 1usize;
v___x_103_ = lean_usize_add(v_i_97_, v___x_102_);
v_i_97_ = v___x_103_;
v_b_99_ = v___y_101_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__10___boxed(mut v_as_112_: *mut lean_object, mut v_i_113_: *mut lean_object, mut v_stop_114_: *mut lean_object, mut v_b_115_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_116_: usize = 0; let mut v_stop_boxed_117_: usize = 0; let mut v_res_118_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_116_ = lean_unbox_usize(v_i_113_);
lean_dec(v_i_113_);
v_stop_boxed_117_ = lean_unbox_usize(v_stop_114_);
lean_dec(v_stop_114_);
v_res_118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__10(v_as_112_, v_i_boxed_116_, v_stop_boxed_117_, v_b_115_);
lean_dec_ref(v_as_112_);
return v_res_118_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__2(mut v_s_119_: *mut lean_object) -> *mut lean_object{
let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_122_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); 
v___x_121_ = lean_get_stdout();
v_putStr_122_ = lean_ctor_get(v___x_121_, 4);
lean_inc_ref(v_putStr_122_);
lean_dec_ref(v___x_121_);
v___x_123_ = lean_apply_2(v_putStr_122_, v_s_119_, lean_box(0));
return v___x_123_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__2___boxed(mut v_s_124_: *mut lean_object, mut v_a_125_: *mut lean_object) -> *mut lean_object{
let mut v_res_126_: *mut lean_object = core::ptr::null_mut(); 
v_res_126_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__2(v_s_124_);
return v_res_126_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_127_: *mut lean_object) -> *mut lean_object{
let mut v___x_129_: u32 = 0; let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); 
v___x_129_ = 10;
v___x_130_ = lean_string_push(v_s_127_, v___x_129_);
v___x_131_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__2(v___x_130_);
return v___x_131_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_132_: *mut lean_object, mut v_a_133_: *mut lean_object) -> *mut lean_object{
let mut v_res_134_: *mut lean_object = core::ptr::null_mut(); 
v_res_134_ = l_IO_println___at___00main_spec__1(v_s_132_);
return v_res_134_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__6_spec__8_spec__9(mut v_x_136_: *mut lean_object, mut v_x_137_: *mut lean_object) -> *mut lean_object{
let mut v_head_138_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_137_) == 0 {
return v_x_136_;
} else {
let mut v_head_138_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); 
v_head_138_ = lean_ctor_get(v_x_137_, 0);
v_tail_139_ = lean_ctor_get(v_x_137_, 1);
v___x_140_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__6_spec__8_spec__9___closed__0;
v___x_141_ = lean_string_append(v_x_136_, v___x_140_);
v___x_142_ = lean_string_append(v___x_141_, v_head_138_);
v_x_136_ = v___x_142_;
v_x_137_ = v_tail_139_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__6_spec__8_spec__9___boxed(mut v_x_144_: *mut lean_object, mut v_x_145_: *mut lean_object) -> *mut lean_object{
let mut v_res_146_: *mut lean_object = core::ptr::null_mut(); 
v_res_146_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__6_spec__8_spec__9(v_x_144_, v_x_145_);
lean_dec(v_x_145_);
return v_res_146_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00main_spec__6_spec__8(mut v_x_150_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_150_) == 0 {
let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); 
v___x_151_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__0;
return v___x_151_;
} else {
let mut v_tail_152_: *mut lean_object = core::ptr::null_mut(); 
v_tail_152_ = lean_ctor_get(v_x_150_, 1);
if lean_obj_tag(v_tail_152_) == 0 {
let mut v_head_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); 
v_head_153_ = lean_ctor_get(v_x_150_, 0);
v___x_154_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__1;
v___x_155_ = lean_string_append(v___x_154_, v_head_153_);
v___x_156_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__2;
v___x_157_ = lean_string_append(v___x_155_, v___x_156_);
return v___x_157_;
} else {
let mut v_head_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v___x_162_: u32 = 0; let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); 
v_head_158_ = lean_ctor_get(v_x_150_, 0);
v___x_159_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__1;
v___x_160_ = lean_string_append(v___x_159_, v_head_158_);
v___x_161_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__6_spec__8_spec__9(v___x_160_, v_tail_152_);
v___x_162_ = 93;
v___x_163_ = lean_string_push(v___x_161_, v___x_162_);
return v___x_163_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___boxed(mut v_x_164_: *mut lean_object) -> *mut lean_object{
let mut v_res_165_: *mut lean_object = core::ptr::null_mut(); 
v_res_165_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8(v_x_164_);
lean_dec(v_x_164_);
return v_res_165_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__6(mut v_s_167_: *mut lean_object) -> *mut lean_object{
let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v___x_172_: *mut lean_object = core::ptr::null_mut(); let mut v___x_173_: u32 = 0; let mut v___x_174_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); 
v___x_169_ = l_IO_println___at___00main_spec__6___closed__0;
v___x_170_ = lean_array_to_list(v_s_167_);
v___x_171_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8(v___x_170_);
lean_dec(v___x_170_);
v___x_172_ = lean_string_append(v___x_169_, v___x_171_);
lean_dec_ref(v___x_171_);
v___x_173_ = 10;
v___x_174_ = lean_string_push(v___x_172_, v___x_173_);
v___x_175_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__2(v___x_174_);
return v___x_175_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__6___boxed(mut v_s_176_: *mut lean_object, mut v_a_177_: *mut lean_object) -> *mut lean_object{
let mut v_res_178_: *mut lean_object = core::ptr::null_mut(); 
v_res_178_ = l_IO_println___at___00main_spec__6(v_s_176_);
return v_res_178_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__8(mut v_as_179_: *mut lean_object, mut v_i_180_: usize, mut v_stop_181_: usize, mut v_b_182_: *mut lean_object) -> *mut lean_object{
let mut v___y_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: usize = 0; let mut v___x_186_: usize = 0; let mut v___x_188_: u8 = 0; let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: u8 = 0; let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_188_ = lean_usize_dec_eq(v_i_180_, v_stop_181_);
if v___x_188_ == 0 {
let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: u8 = 0; 
v___x_189_ = lean_array_uget_borrowed(v_as_179_, v_i_180_);
v___x_190_ = lean_unsigned_to_nat(10);
v___x_191_ = lean_nat_dec_lt(v___x_190_, v___x_189_);
if v___x_191_ == 0 {
v___y_184_ = v_b_182_;
state = 1; continue;
} else {
let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v___x_189_);
v___x_192_ = lean_array_push(v_b_182_, v___x_189_);
v___y_184_ = v___x_192_;
state = 1; continue;
}
} else {
return v_b_182_;
}
}
1 => {
v___x_185_ = 1usize;
v___x_186_ = lean_usize_add(v_i_180_, v___x_185_);
v_i_180_ = v___x_186_;
v_b_182_ = v___y_184_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__8___boxed(mut v_as_193_: *mut lean_object, mut v_i_194_: *mut lean_object, mut v_stop_195_: *mut lean_object, mut v_b_196_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_197_: usize = 0; let mut v_stop_boxed_198_: usize = 0; let mut v_res_199_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_197_ = lean_unbox_usize(v_i_194_);
lean_dec(v_i_194_);
v_stop_boxed_198_ = lean_unbox_usize(v_stop_195_);
lean_dec(v_stop_195_);
v_res_199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__8(v_as_193_, v_i_boxed_197_, v_stop_boxed_198_, v_b_196_);
lean_dec_ref(v_as_193_);
return v_res_199_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__7(mut v_as_200_: *mut lean_object, mut v_i_201_: usize, mut v_stop_202_: usize, mut v_b_203_: *mut lean_object) -> *mut lean_object{
let mut v___y_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: usize = 0; let mut v___x_207_: usize = 0; let mut v___x_209_: u8 = 0; let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: u8 = 0; let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_209_ = lean_usize_dec_eq(v_i_201_, v_stop_202_);
if v___x_209_ == 0 {
let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___x_212_: u8 = 0; 
v___x_210_ = lean_unsigned_to_nat(0);
v___x_211_ = lean_array_uget_borrowed(v_as_200_, v_i_201_);
v___x_212_ = lean_nat_dec_lt(v___x_210_, v___x_211_);
if v___x_212_ == 0 {
v___y_205_ = v_b_203_;
state = 1; continue;
} else {
let mut v___x_213_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v___x_211_);
v___x_213_ = lean_array_push(v_b_203_, v___x_211_);
v___y_205_ = v___x_213_;
state = 1; continue;
}
} else {
return v_b_203_;
}
}
1 => {
v___x_206_ = 1usize;
v___x_207_ = lean_usize_add(v_i_201_, v___x_206_);
v_i_201_ = v___x_207_;
v_b_203_ = v___y_205_;
state = 0; continue;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__7___boxed(mut v_as_214_: *mut lean_object, mut v_i_215_: *mut lean_object, mut v_stop_216_: *mut lean_object, mut v_b_217_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_218_: usize = 0; let mut v_stop_boxed_219_: usize = 0; let mut v_res_220_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_218_ = lean_unbox_usize(v_i_215_);
lean_dec(v_i_215_);
v_stop_boxed_219_ = lean_unbox_usize(v_stop_216_);
lean_dec(v_stop_216_);
v_res_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__7(v_as_214_, v_i_boxed_218_, v_stop_boxed_219_, v_b_217_);
lean_dec_ref(v_as_214_);
return v_res_220_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(mut v_sz_221_: usize, mut v_i_222_: usize, mut v_bs_223_: *mut lean_object) -> *mut lean_object{
let mut v___x_224_: u8 = 0; let mut v_v_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); let mut v_bs_x27_227_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: usize = 0; let mut v___x_231_: usize = 0; let mut v___x_232_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_224_ = lean_usize_dec_lt(v_i_222_, v_sz_221_);
if v___x_224_ == 0 {
return v_bs_223_;
} else {
let mut v_v_225_: *mut lean_object = core::ptr::null_mut(); let mut v___x_226_: *mut lean_object = core::ptr::null_mut(); let mut v_bs_x27_227_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: usize = 0; let mut v___x_231_: usize = 0; let mut v___x_232_: *mut lean_object = core::ptr::null_mut(); 
v_v_225_ = lean_array_uget(v_bs_223_, v_i_222_);
v___x_226_ = lean_unsigned_to_nat(0);
v_bs_x27_227_ = lean_array_uset(v_bs_223_, v_i_222_, v___x_226_);
v___x_228_ = lean_unsigned_to_nat(10);
v___x_229_ = lean_nat_add(v_v_225_, v___x_228_);
lean_dec(v_v_225_);
v___x_230_ = 1usize;
v___x_231_ = lean_usize_add(v_i_222_, v___x_230_);
v___x_232_ = lean_array_uset(v_bs_x27_227_, v_i_222_, v___x_229_);
v_i_222_ = v___x_231_;
v_bs_223_ = v___x_232_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___boxed(mut v_sz_234_: *mut lean_object, mut v_i_235_: *mut lean_object, mut v_bs_236_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_237_: usize = 0; let mut v_i_boxed_238_: usize = 0; let mut v_res_239_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_237_ = lean_unbox_usize(v_sz_234_);
lean_dec(v_sz_234_);
v_i_boxed_238_ = lean_unbox_usize(v_i_235_);
lean_dec(v_i_235_);
v_res_239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_boxed_237_, v_i_boxed_238_, v_bs_236_);
return v_res_239_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__5(mut v_sz_240_: usize, mut v_i_241_: usize, mut v_bs_242_: *mut lean_object) -> *mut lean_object{
let mut v___x_243_: u8 = 0; let mut v_v_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_245_: *mut lean_object = core::ptr::null_mut(); let mut v_bs_x27_246_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v___x_248_: usize = 0; let mut v___x_249_: usize = 0; let mut v___x_250_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_243_ = lean_usize_dec_lt(v_i_241_, v_sz_240_);
if v___x_243_ == 0 {
return v_bs_242_;
} else {
let mut v_v_244_: *mut lean_object = core::ptr::null_mut(); let mut v___x_245_: *mut lean_object = core::ptr::null_mut(); let mut v_bs_x27_246_: *mut lean_object = core::ptr::null_mut(); let mut v___x_247_: *mut lean_object = core::ptr::null_mut(); let mut v___x_248_: usize = 0; let mut v___x_249_: usize = 0; let mut v___x_250_: *mut lean_object = core::ptr::null_mut(); 
v_v_244_ = lean_array_uget(v_bs_242_, v_i_241_);
v___x_245_ = lean_unsigned_to_nat(0);
v_bs_x27_246_ = lean_array_uset(v_bs_242_, v_i_241_, v___x_245_);
v___x_247_ = l_Nat_reprFast(v_v_244_);
v___x_248_ = 1usize;
v___x_249_ = lean_usize_add(v_i_241_, v___x_248_);
v___x_250_ = lean_array_uset(v_bs_x27_246_, v_i_241_, v___x_247_);
v_i_241_ = v___x_249_;
v_bs_242_ = v___x_250_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__5___boxed(mut v_sz_252_: *mut lean_object, mut v_i_253_: *mut lean_object, mut v_bs_254_: *mut lean_object) -> *mut lean_object{
let mut v_sz_boxed_255_: usize = 0; let mut v_i_boxed_256_: usize = 0; let mut v_res_257_: *mut lean_object = core::ptr::null_mut(); 
v_sz_boxed_255_ = lean_unbox_usize(v_sz_252_);
lean_dec(v_sz_252_);
v_i_boxed_256_ = lean_unbox_usize(v_i_253_);
lean_dec(v_i_253_);
v_res_257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__5(v_sz_boxed_255_, v_i_boxed_256_, v_bs_254_);
return v_res_257_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00main_spec__0_spec__0(mut v_x_258_: *mut lean_object, mut v_x_259_: *mut lean_object) -> *mut lean_object{
let mut v_head_260_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_261_: *mut lean_object = core::ptr::null_mut(); let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_259_) == 0 {
return v_x_258_;
} else {
let mut v_head_260_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_261_: *mut lean_object = core::ptr::null_mut(); let mut v___x_262_: *mut lean_object = core::ptr::null_mut(); let mut v___x_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: *mut lean_object = core::ptr::null_mut(); let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); 
v_head_260_ = lean_ctor_get(v_x_259_, 0);
lean_inc(v_head_260_);
v_tail_261_ = lean_ctor_get(v_x_259_, 1);
lean_inc(v_tail_261_);
lean_dec_ref_known(v_x_259_, 2);
v___x_262_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__6_spec__8_spec__9___closed__0;
v___x_263_ = lean_string_append(v_x_258_, v___x_262_);
v___x_264_ = l_Nat_reprFast(v_head_260_);
v___x_265_ = lean_string_append(v___x_263_, v___x_264_);
lean_dec_ref(v___x_264_);
v_x_258_ = v___x_265_;
v_x_259_ = v_tail_261_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00main_spec__0(mut v_x_267_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_267_) == 0 {
let mut v___x_268_: *mut lean_object = core::ptr::null_mut(); 
v___x_268_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__0;
return v___x_268_;
} else {
let mut v_tail_269_: *mut lean_object = core::ptr::null_mut(); 
v_tail_269_ = lean_ctor_get(v_x_267_, 1);
if lean_obj_tag(v_tail_269_) == 0 {
let mut v_head_270_: *mut lean_object = core::ptr::null_mut(); let mut v___x_271_: *mut lean_object = core::ptr::null_mut(); let mut v___x_272_: *mut lean_object = core::ptr::null_mut(); let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v___x_274_: *mut lean_object = core::ptr::null_mut(); let mut v___x_275_: *mut lean_object = core::ptr::null_mut(); 
v_head_270_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_head_270_);
lean_dec_ref_known(v_x_267_, 2);
v___x_271_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__1;
v___x_272_ = l_Nat_reprFast(v_head_270_);
v___x_273_ = lean_string_append(v___x_271_, v___x_272_);
lean_dec_ref(v___x_272_);
v___x_274_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__2;
v___x_275_ = lean_string_append(v___x_273_, v___x_274_);
return v___x_275_;
} else {
let mut v_head_276_: *mut lean_object = core::ptr::null_mut(); let mut v___x_277_: *mut lean_object = core::ptr::null_mut(); let mut v___x_278_: *mut lean_object = core::ptr::null_mut(); let mut v___x_279_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: *mut lean_object = core::ptr::null_mut(); let mut v___x_281_: u32 = 0; let mut v___x_282_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_tail_269_);
v_head_276_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_head_276_);
lean_dec_ref_known(v_x_267_, 2);
v___x_277_ = l_List_toString___at___00IO_println___at___00main_spec__6_spec__8___closed__1;
v___x_278_ = l_Nat_reprFast(v_head_276_);
v___x_279_ = lean_string_append(v___x_277_, v___x_278_);
lean_dec_ref(v___x_278_);
v___x_280_ = l_List_foldl___at___00List_toString___at___00main_spec__0_spec__0(v___x_279_, v_tail_269_);
v___x_281_ = 93;
v___x_282_ = lean_string_push(v___x_280_, v___x_281_);
return v___x_282_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__3(mut v_s_283_: *mut lean_object) -> *mut lean_object{
let mut v___x_285_: *mut lean_object = core::ptr::null_mut(); let mut v___x_286_: *mut lean_object = core::ptr::null_mut(); let mut v___x_287_: *mut lean_object = core::ptr::null_mut(); let mut v___x_288_: *mut lean_object = core::ptr::null_mut(); let mut v___x_289_: u32 = 0; let mut v___x_290_: *mut lean_object = core::ptr::null_mut(); let mut v___x_291_: *mut lean_object = core::ptr::null_mut(); 
v___x_285_ = l_IO_println___at___00main_spec__6___closed__0;
v___x_286_ = lean_array_to_list(v_s_283_);
v___x_287_ = l_List_toString___at___00main_spec__0(v___x_286_);
v___x_288_ = lean_string_append(v___x_285_, v___x_287_);
lean_dec_ref(v___x_287_);
v___x_289_ = 10;
v___x_290_ = lean_string_push(v___x_288_, v___x_289_);
v___x_291_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__2(v___x_290_);
return v___x_291_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__3___boxed(mut v_s_292_: *mut lean_object, mut v_a_293_: *mut lean_object) -> *mut lean_object{
let mut v_res_294_: *mut lean_object = core::ptr::null_mut(); 
v_res_294_ = l_IO_println___at___00main_spec__3(v_s_292_);
return v_res_294_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v_a_297_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); 
v_a_297_ = l_main___closed__0;
v___x_298_ = lean_array_to_list(v_a_297_);
return v___x_298_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_299_: *mut lean_object = core::ptr::null_mut(); let mut v___x_300_: *mut lean_object = core::ptr::null_mut(); 
v___x_299_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_300_ = l_List_toString___at___00main_spec__0(v___x_299_);
return v___x_300_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> *mut lean_object{
let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); let mut v___x_302_: *mut lean_object = core::ptr::null_mut(); let mut v___x_303_: *mut lean_object = core::ptr::null_mut(); 
v___x_301_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_302_ = l_IO_println___at___00main_spec__6___closed__0;
v___x_303_ = lean_string_append(v___x_302_, v___x_301_);
return v___x_303_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> *mut lean_object{
let mut v_a_304_: *mut lean_object = core::ptr::null_mut(); let mut v___x_305_: *mut lean_object = core::ptr::null_mut(); 
v_a_304_ = l_main___closed__0;
v___x_305_ = lean_array_get_size(v_a_304_);
return v___x_305_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_306_: *mut lean_object = core::ptr::null_mut(); let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); 
v___x_306_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___x_307_ = l_Nat_reprFast(v___x_306_);
return v___x_307_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> *mut lean_object{
let mut v_a_308_: *mut lean_object = core::ptr::null_mut(); let mut v___x_309_: *mut lean_object = core::ptr::null_mut(); 
v_a_308_ = l_main___closed__0;
v___x_309_ = l_foo(v_a_308_);
return v___x_309_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__7() -> *mut lean_object{
let mut v___x_310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_311_: *mut lean_object = core::ptr::null_mut(); 
v___x_310_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v___x_311_ = lean_array_to_list(v___x_310_);
return v___x_311_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8() -> *mut lean_object{
let mut v___x_312_: *mut lean_object = core::ptr::null_mut(); let mut v___x_313_: *mut lean_object = core::ptr::null_mut(); 
v___x_312_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_313_ = l_List_toString___at___00main_spec__0(v___x_312_);
return v___x_313_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__9() -> *mut lean_object{
let mut v___x_314_: *mut lean_object = core::ptr::null_mut(); let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); let mut v___x_316_: *mut lean_object = core::ptr::null_mut(); 
v___x_314_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_315_ = l_IO_println___at___00main_spec__6___closed__0;
v___x_316_ = lean_string_append(v___x_315_, v___x_314_);
return v___x_316_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10() -> usize{
let mut v___x_317_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_318_: usize = 0; 
v___x_317_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v_sz_318_ = lean_array_size(v___x_317_);
return v_sz_318_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__11() -> *mut lean_object{
let mut v___x_319_: *mut lean_object = core::ptr::null_mut(); let mut v___x_320_: usize = 0; let mut v_sz_321_: usize = 0; let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); 
v___x_319_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v___x_320_ = 0usize;
v_sz_321_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_321_, v___x_320_, v___x_319_);
return v___x_322_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__12() -> *mut lean_object{
let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); let mut v___x_324_: *mut lean_object = core::ptr::null_mut(); 
v___x_323_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v___x_324_ = lean_array_to_list(v___x_323_);
return v___x_324_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__13() -> *mut lean_object{
let mut v___x_325_: *mut lean_object = core::ptr::null_mut(); let mut v___x_326_: *mut lean_object = core::ptr::null_mut(); 
v___x_325_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_326_ = l_List_toString___at___00main_spec__0(v___x_325_);
return v___x_326_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__14() -> *mut lean_object{
let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); 
v___x_327_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__13), core::ptr::addr_of_mut!(l_main___closed__13_once), _init_l_main___closed__13);
v___x_328_ = l_IO_println___at___00main_spec__6___closed__0;
v___x_329_ = lean_string_append(v___x_328_, v___x_327_);
return v___x_329_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__15() -> *mut lean_object{
let mut v___x_330_: *mut lean_object = core::ptr::null_mut(); let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); 
v___x_330_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v___x_331_ = lean_array_get_size(v___x_330_);
return v___x_331_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__16() -> *mut lean_object{
let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); let mut v___x_333_: *mut lean_object = core::ptr::null_mut(); 
v___x_332_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__15), core::ptr::addr_of_mut!(l_main___closed__15_once), _init_l_main___closed__15);
v___x_333_ = l_Nat_reprFast(v___x_332_);
return v___x_333_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__17() -> *mut lean_object{
let mut v___x_334_: *mut lean_object = core::ptr::null_mut(); let mut v___x_335_: *mut lean_object = core::ptr::null_mut(); 
v___x_334_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v___x_335_ = lean_array_pop(v___x_334_);
return v___x_335_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__18() -> *mut lean_object{
let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); 
v___x_336_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
v___x_337_ = lean_array_to_list(v___x_336_);
return v___x_337_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__19() -> *mut lean_object{
let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_339_: *mut lean_object = core::ptr::null_mut(); 
v___x_338_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__18), core::ptr::addr_of_mut!(l_main___closed__18_once), _init_l_main___closed__18);
v___x_339_ = l_List_toString___at___00main_spec__0(v___x_338_);
return v___x_339_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__20() -> *mut lean_object{
let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: *mut lean_object = core::ptr::null_mut(); 
v___x_340_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__19), core::ptr::addr_of_mut!(l_main___closed__19_once), _init_l_main___closed__19);
v___x_341_ = l_IO_println___at___00main_spec__6___closed__0;
v___x_342_ = lean_string_append(v___x_341_, v___x_340_);
return v___x_342_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__21() -> *mut lean_object{
let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_344_: *mut lean_object = core::ptr::null_mut(); let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); 
v___x_343_ = lean_unsigned_to_nat(100);
v___x_344_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v___x_345_ = lean_array_push(v___x_344_, v___x_343_);
return v___x_345_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__22() -> *mut lean_object{
let mut v___x_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_347_: *mut lean_object = core::ptr::null_mut(); 
v___x_346_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__21), core::ptr::addr_of_mut!(l_main___closed__21_once), _init_l_main___closed__21);
v___x_347_ = lean_array_to_list(v___x_346_);
return v___x_347_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__23() -> *mut lean_object{
let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); let mut v___x_349_: *mut lean_object = core::ptr::null_mut(); 
v___x_348_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__22), core::ptr::addr_of_mut!(l_main___closed__22_once), _init_l_main___closed__22);
v___x_349_ = l_List_toString___at___00main_spec__0(v___x_348_);
return v___x_349_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__24() -> *mut lean_object{
let mut v___x_350_: *mut lean_object = core::ptr::null_mut(); let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v___x_352_: *mut lean_object = core::ptr::null_mut(); 
v___x_350_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__23), core::ptr::addr_of_mut!(l_main___closed__23_once), _init_l_main___closed__23);
v___x_351_ = l_IO_println___at___00main_spec__6___closed__0;
v___x_352_ = lean_string_append(v___x_351_, v___x_350_);
return v___x_352_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__26() -> usize{
let mut v___x_362_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_363_: usize = 0; 
v___x_362_ = l_main___closed__25;
v_sz_363_ = lean_array_size(v___x_362_);
return v_sz_363_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__27() -> *mut lean_object{
let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); let mut v___x_365_: usize = 0; let mut v_sz_366_: usize = 0; let mut v___x_367_: *mut lean_object = core::ptr::null_mut(); 
v___x_364_ = l_main___closed__25;
v___x_365_ = 0usize;
v_sz_366_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__26), core::ptr::addr_of_mut!(l_main___closed__26_once), _init_l_main___closed__26);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__4(v_sz_366_, v___x_365_, v___x_364_);
return v___x_367_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__28() -> usize{
let mut v___x_368_: *mut lean_object = core::ptr::null_mut(); let mut v_sz_369_: usize = 0; 
v___x_368_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__27), core::ptr::addr_of_mut!(l_main___closed__27_once), _init_l_main___closed__27);
v_sz_369_ = lean_array_size(v___x_368_);
return v_sz_369_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__29() -> *mut lean_object{
let mut v___x_370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_371_: usize = 0; let mut v_sz_372_: usize = 0; let mut v___x_373_: *mut lean_object = core::ptr::null_mut(); 
v___x_370_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__27), core::ptr::addr_of_mut!(l_main___closed__27_once), _init_l_main___closed__27);
v___x_371_ = 0usize;
v_sz_372_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__28), core::ptr::addr_of_mut!(l_main___closed__28_once), _init_l_main___closed__28);
v___x_373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__5(v_sz_372_, v___x_371_, v___x_370_);
return v___x_373_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__30() -> *mut lean_object{
let mut v___x_374_: *mut lean_object = core::ptr::null_mut(); let mut v___x_375_: *mut lean_object = core::ptr::null_mut(); let mut v___x_376_: *mut lean_object = core::ptr::null_mut(); let mut v___x_377_: *mut lean_object = core::ptr::null_mut(); 
v___x_374_ = lean_unsigned_to_nat(3);
v___x_375_ = lean_unsigned_to_nat(1);
v___x_376_ = l_main___closed__25;
v___x_377_ = l_Array_extract___redArg(v___x_376_, v___x_375_, v___x_374_);
return v___x_377_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__31() -> *mut lean_object{
let mut v___x_378_: *mut lean_object = core::ptr::null_mut(); let mut v___x_379_: *mut lean_object = core::ptr::null_mut(); let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); let mut v___x_381_: *mut lean_object = core::ptr::null_mut(); 
v___x_378_ = lean_unsigned_to_nat(100);
v___x_379_ = lean_unsigned_to_nat(0);
v___x_380_ = l_main___closed__25;
v___x_381_ = l_Array_extract___redArg(v___x_380_, v___x_379_, v___x_378_);
return v___x_381_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__32() -> *mut lean_object{
let mut v___x_382_: *mut lean_object = core::ptr::null_mut(); let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v___x_384_: *mut lean_object = core::ptr::null_mut(); 
v___x_382_ = lean_unsigned_to_nat(1);
v___x_383_ = l_main___closed__25;
v___x_384_ = l_Array_extract___redArg(v___x_383_, v___x_382_, v___x_382_);
return v___x_384_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__33() -> *mut lean_object{
let mut v___x_385_: *mut lean_object = core::ptr::null_mut(); let mut v___x_386_: *mut lean_object = core::ptr::null_mut(); let mut v___x_387_: *mut lean_object = core::ptr::null_mut(); let mut v___x_388_: *mut lean_object = core::ptr::null_mut(); 
v___x_385_ = lean_unsigned_to_nat(4);
v___x_386_ = lean_unsigned_to_nat(2);
v___x_387_ = l_main___closed__25;
v___x_388_ = l_Array_extract___redArg(v___x_387_, v___x_386_, v___x_385_);
return v___x_388_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__34() -> *mut lean_object{
let mut v___x_389_: *mut lean_object = core::ptr::null_mut(); let mut v___x_390_: *mut lean_object = core::ptr::null_mut(); 
v___x_389_ = l_main___closed__25;
v___x_390_ = l_Array_reverse___redArg(v___x_389_);
return v___x_390_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__36() -> *mut lean_object{
let mut v___x_393_: *mut lean_object = core::ptr::null_mut(); let mut v___x_394_: *mut lean_object = core::ptr::null_mut(); 
v___x_393_ = l_main___closed__35;
v___x_394_ = l_Array_reverse___redArg(v___x_393_);
return v___x_394_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__38() -> *mut lean_object{
let mut v___x_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_403_: *mut lean_object = core::ptr::null_mut(); 
v___x_402_ = l_main___closed__37;
v___x_403_ = l_Array_reverse___redArg(v___x_402_);
return v___x_403_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__39() -> *mut lean_object{
let mut v___x_404_: *mut lean_object = core::ptr::null_mut(); let mut v___x_405_: *mut lean_object = core::ptr::null_mut(); 
v___x_404_ = l_main___closed__25;
v___x_405_ = lean_array_get_size(v___x_404_);
return v___x_405_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__40() -> u8{
let mut v___x_406_: *mut lean_object = core::ptr::null_mut(); let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v___x_408_: u8 = 0; 
v___x_406_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__39), core::ptr::addr_of_mut!(l_main___closed__39_once), _init_l_main___closed__39);
v___x_407_ = lean_unsigned_to_nat(0);
v___x_408_ = lean_nat_dec_lt(v___x_407_, v___x_406_);
return v___x_408_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__41() -> u8{
let mut v___x_409_: *mut lean_object = core::ptr::null_mut(); let mut v___x_410_: u8 = 0; 
v___x_409_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__39), core::ptr::addr_of_mut!(l_main___closed__39_once), _init_l_main___closed__39);
v___x_410_ = lean_nat_dec_le(v___x_409_, v___x_409_);
return v___x_410_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__42() -> usize{
let mut v___x_411_: *mut lean_object = core::ptr::null_mut(); let mut v___x_412_: usize = 0; 
v___x_411_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__39), core::ptr::addr_of_mut!(l_main___closed__39_once), _init_l_main___closed__39);
v___x_412_ = lean_usize_of_nat(v___x_411_);
return v___x_412_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__43() -> *mut lean_object{
let mut v___x_413_: *mut lean_object = core::ptr::null_mut(); let mut v___x_414_: usize = 0; let mut v___x_415_: usize = 0; let mut v___x_416_: *mut lean_object = core::ptr::null_mut(); let mut v___x_417_: *mut lean_object = core::ptr::null_mut(); 
v___x_413_ = l_main___closed__35;
v___x_414_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__42), core::ptr::addr_of_mut!(l_main___closed__42_once), _init_l_main___closed__42);
v___x_415_ = 0usize;
v___x_416_ = l_main___closed__25;
v___x_417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__7(v___x_416_, v___x_415_, v___x_414_, v___x_413_);
return v___x_417_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__44() -> *mut lean_object{
let mut v___x_418_: *mut lean_object = core::ptr::null_mut(); let mut v___x_419_: usize = 0; let mut v___x_420_: usize = 0; let mut v___x_421_: *mut lean_object = core::ptr::null_mut(); let mut v___x_422_: *mut lean_object = core::ptr::null_mut(); 
v___x_418_ = l_main___closed__35;
v___x_419_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__42), core::ptr::addr_of_mut!(l_main___closed__42_once), _init_l_main___closed__42);
v___x_420_ = 0usize;
v___x_421_ = l_main___closed__25;
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__8(v___x_421_, v___x_420_, v___x_419_, v___x_418_);
return v___x_422_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__45() -> *mut lean_object{
let mut v___x_423_: *mut lean_object = core::ptr::null_mut(); let mut v___x_424_: usize = 0; let mut v___x_425_: usize = 0; let mut v___x_426_: *mut lean_object = core::ptr::null_mut(); let mut v___x_427_: *mut lean_object = core::ptr::null_mut(); 
v___x_423_ = l_main___closed__35;
v___x_424_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__42), core::ptr::addr_of_mut!(l_main___closed__42_once), _init_l_main___closed__42);
v___x_425_ = 0usize;
v___x_426_ = l_main___closed__25;
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__9(v___x_426_, v___x_425_, v___x_424_, v___x_423_);
return v___x_427_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__47() -> *mut lean_object{
let mut v___x_439_: *mut lean_object = core::ptr::null_mut(); let mut v___x_440_: *mut lean_object = core::ptr::null_mut(); 
v___x_439_ = l_main___closed__46;
v___x_440_ = lean_array_get_size(v___x_439_);
return v___x_440_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__48() -> u8{
let mut v___x_441_: *mut lean_object = core::ptr::null_mut(); let mut v___x_442_: *mut lean_object = core::ptr::null_mut(); let mut v___x_443_: u8 = 0; 
v___x_441_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__47), core::ptr::addr_of_mut!(l_main___closed__47_once), _init_l_main___closed__47);
v___x_442_ = lean_unsigned_to_nat(0);
v___x_443_ = lean_nat_dec_lt(v___x_442_, v___x_441_);
return v___x_443_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__49() -> u8{
let mut v___x_444_: *mut lean_object = core::ptr::null_mut(); let mut v___x_445_: u8 = 0; 
v___x_444_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__47), core::ptr::addr_of_mut!(l_main___closed__47_once), _init_l_main___closed__47);
v___x_445_ = lean_nat_dec_le(v___x_444_, v___x_444_);
return v___x_445_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__50() -> usize{
let mut v___x_446_: *mut lean_object = core::ptr::null_mut(); let mut v___x_447_: usize = 0; 
v___x_446_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__47), core::ptr::addr_of_mut!(l_main___closed__47_once), _init_l_main___closed__47);
v___x_447_ = lean_usize_of_nat(v___x_446_);
return v___x_447_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__51() -> *mut lean_object{
let mut v___x_448_: *mut lean_object = core::ptr::null_mut(); let mut v___x_449_: usize = 0; let mut v___x_450_: usize = 0; let mut v___x_451_: *mut lean_object = core::ptr::null_mut(); let mut v___x_452_: *mut lean_object = core::ptr::null_mut(); 
v___x_448_ = l_main___closed__35;
v___x_449_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__50), core::ptr::addr_of_mut!(l_main___closed__50_once), _init_l_main___closed__50);
v___x_450_ = 0usize;
v___x_451_ = l_main___closed__46;
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__11(v___x_451_, v___x_450_, v___x_449_, v___x_448_);
return v___x_452_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__52() -> *mut lean_object{
let mut v___x_453_: *mut lean_object = core::ptr::null_mut(); let mut v___x_454_: usize = 0; let mut v___x_455_: usize = 0; let mut v___x_456_: *mut lean_object = core::ptr::null_mut(); let mut v___x_457_: *mut lean_object = core::ptr::null_mut(); 
v___x_453_ = l_main___closed__35;
v___x_454_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__42), core::ptr::addr_of_mut!(l_main___closed__42_once), _init_l_main___closed__42);
v___x_455_ = 0usize;
v___x_456_ = l_main___closed__25;
v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__11(v___x_456_, v___x_455_, v___x_454_, v___x_453_);
return v___x_457_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_458_: u32 = 0; let mut v___x_459_: *mut lean_object = core::ptr::null_mut(); 
v___x_458_ = 0;
v___x_459_ = lean_box_uint32(v___x_458_);
return v___x_459_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___y_462_: *mut lean_object = core::ptr::null_mut(); let mut v___x_463_: *mut lean_object = core::ptr::null_mut(); let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_466_: u8 = 0; let mut v___x_467_: *mut lean_object = core::ptr::null_mut(); let mut v___x_469_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_470_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_471_: u8 = 0; let mut v_unused_472_: *mut lean_object = core::ptr::null_mut(); let mut v_a_473_: *mut lean_object = core::ptr::null_mut(); let mut v___x_475_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_476_: u8 = 0; let mut v___x_478_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_479_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_480_: u8 = 0; let mut v___x_481_: *mut lean_object = core::ptr::null_mut(); let mut v___x_482_: *mut lean_object = core::ptr::null_mut(); let mut v___x_483_: *mut lean_object = core::ptr::null_mut(); let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); let mut v___x_486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); let mut v___x_488_: usize = 0; let mut v___x_489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); let mut v___x_491_: *mut lean_object = core::ptr::null_mut(); let mut v___x_492_: *mut lean_object = core::ptr::null_mut(); let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); let mut v___x_496_: *mut lean_object = core::ptr::null_mut(); let mut v___x_497_: *mut lean_object = core::ptr::null_mut(); let mut v___x_498_: *mut lean_object = core::ptr::null_mut(); let mut v___x_499_: *mut lean_object = core::ptr::null_mut(); let mut v___x_500_: *mut lean_object = core::ptr::null_mut(); let mut v___x_501_: *mut lean_object = core::ptr::null_mut(); let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); let mut v___x_506_: *mut lean_object = core::ptr::null_mut(); let mut v___x_507_: *mut lean_object = core::ptr::null_mut(); let mut v___x_508_: *mut lean_object = core::ptr::null_mut(); let mut v___x_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); let mut v___x_513_: *mut lean_object = core::ptr::null_mut(); let mut v___x_514_: *mut lean_object = core::ptr::null_mut(); let mut v___x_515_: *mut lean_object = core::ptr::null_mut(); let mut v___y_517_: *mut lean_object = core::ptr::null_mut(); let mut v___x_518_: *mut lean_object = core::ptr::null_mut(); let mut v___x_519_: u8 = 0; let mut v___x_520_: u8 = 0; let mut v___x_521_: *mut lean_object = core::ptr::null_mut(); let mut v___x_522_: *mut lean_object = core::ptr::null_mut(); let mut v_a_523_: *mut lean_object = core::ptr::null_mut(); let mut v___x_525_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_526_: u8 = 0; let mut v___x_528_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_529_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_530_: u8 = 0; let mut v___y_532_: *mut lean_object = core::ptr::null_mut(); let mut v___x_533_: *mut lean_object = core::ptr::null_mut(); let mut v___x_534_: u8 = 0; let mut v___x_535_: u8 = 0; let mut v___x_536_: *mut lean_object = core::ptr::null_mut(); let mut v___x_537_: *mut lean_object = core::ptr::null_mut(); let mut v_a_538_: *mut lean_object = core::ptr::null_mut(); let mut v___x_540_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_541_: u8 = 0; let mut v___x_543_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_544_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_545_: u8 = 0; let mut v___y_547_: *mut lean_object = core::ptr::null_mut(); let mut v___x_548_: *mut lean_object = core::ptr::null_mut(); let mut v___x_549_: u8 = 0; let mut v___x_550_: u8 = 0; let mut v___x_551_: *mut lean_object = core::ptr::null_mut(); let mut v___x_552_: *mut lean_object = core::ptr::null_mut(); let mut v_a_553_: *mut lean_object = core::ptr::null_mut(); let mut v___x_555_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_556_: u8 = 0; let mut v___x_558_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_559_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_560_: u8 = 0; let mut v___y_562_: *mut lean_object = core::ptr::null_mut(); let mut v___y_563_: *mut lean_object = core::ptr::null_mut(); let mut v___y_564_: *mut lean_object = core::ptr::null_mut(); let mut v___x_565_: *mut lean_object = core::ptr::null_mut(); let mut v___x_566_: u8 = 0; let mut v___x_567_: u8 = 0; let mut v___x_568_: usize = 0; let mut v___x_569_: *mut lean_object = core::ptr::null_mut(); let mut v___x_570_: usize = 0; let mut v___x_571_: *mut lean_object = core::ptr::null_mut(); let mut v_a_572_: *mut lean_object = core::ptr::null_mut(); let mut v___x_574_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_575_: u8 = 0; let mut v___x_577_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_578_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_579_: u8 = 0; let mut v___y_581_: *mut lean_object = core::ptr::null_mut(); let mut v___x_582_: *mut lean_object = core::ptr::null_mut(); let mut v___x_583_: *mut lean_object = core::ptr::null_mut(); let mut v___x_584_: *mut lean_object = core::ptr::null_mut(); let mut v___x_585_: u8 = 0; let mut v___x_586_: u8 = 0; let mut v___x_587_: *mut lean_object = core::ptr::null_mut(); let mut v___x_588_: *mut lean_object = core::ptr::null_mut(); let mut v_a_589_: *mut lean_object = core::ptr::null_mut(); let mut v___x_591_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_592_: u8 = 0; let mut v___x_594_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_595_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_596_: u8 = 0; let mut v___x_597_: u8 = 0; let mut v___x_598_: u8 = 0; let mut v___x_599_: *mut lean_object = core::ptr::null_mut(); let mut v___x_600_: *mut lean_object = core::ptr::null_mut(); let mut v_a_601_: *mut lean_object = core::ptr::null_mut(); let mut v___x_603_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_604_: u8 = 0; let mut v___x_606_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_607_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_608_: u8 = 0; let mut v_a_609_: *mut lean_object = core::ptr::null_mut(); let mut v___x_611_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_612_: u8 = 0; let mut v___x_614_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_615_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_616_: u8 = 0; let mut v_a_617_: *mut lean_object = core::ptr::null_mut(); let mut v___x_619_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_620_: u8 = 0; let mut v___x_622_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_623_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_624_: u8 = 0; let mut v_a_625_: *mut lean_object = core::ptr::null_mut(); let mut v___x_627_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_628_: u8 = 0; let mut v___x_630_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_631_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_632_: u8 = 0; let mut v_a_633_: *mut lean_object = core::ptr::null_mut(); let mut v___x_635_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_636_: u8 = 0; let mut v___x_638_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_639_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_640_: u8 = 0; let mut v_a_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_644_: u8 = 0; let mut v___x_646_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_647_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_648_: u8 = 0; let mut v_a_649_: *mut lean_object = core::ptr::null_mut(); let mut v___x_651_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_652_: u8 = 0; let mut v___x_654_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_655_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_656_: u8 = 0; let mut v_a_657_: *mut lean_object = core::ptr::null_mut(); let mut v___x_659_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_660_: u8 = 0; let mut v___x_662_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_663_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_664_: u8 = 0; let mut v_a_665_: *mut lean_object = core::ptr::null_mut(); let mut v___x_667_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_668_: u8 = 0; let mut v___x_670_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_671_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_672_: u8 = 0; let mut v_a_673_: *mut lean_object = core::ptr::null_mut(); let mut v___x_675_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_676_: u8 = 0; let mut v___x_678_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_679_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_680_: u8 = 0; let mut v_a_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_684_: u8 = 0; let mut v___x_686_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_687_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_688_: u8 = 0; let mut v_a_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_691_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_692_: u8 = 0; let mut v___x_694_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_695_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_696_: u8 = 0; let mut v_a_697_: *mut lean_object = core::ptr::null_mut(); let mut v___x_699_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_700_: u8 = 0; let mut v___x_702_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_703_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_704_: u8 = 0; let mut v_a_705_: *mut lean_object = core::ptr::null_mut(); let mut v___x_707_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_708_: u8 = 0; let mut v___x_710_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_711_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_712_: u8 = 0; let mut v_a_713_: *mut lean_object = core::ptr::null_mut(); let mut v___x_715_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_716_: u8 = 0; let mut v___x_718_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_719_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_720_: u8 = 0; let mut v_a_721_: *mut lean_object = core::ptr::null_mut(); let mut v___x_723_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_724_: u8 = 0; let mut v___x_726_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_727_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_728_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_481_ = lean_unsigned_to_nat(0);
v___x_482_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_483_ = l_IO_println___at___00main_spec__1(v___x_482_);
if lean_obj_tag(v___x_483_) == 0 {
let mut v___x_484_: *mut lean_object = core::ptr::null_mut(); let mut v___x_485_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_483_, 1);
v___x_484_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_485_ = l_IO_println___at___00main_spec__1(v___x_484_);
if lean_obj_tag(v___x_485_) == 0 {
let mut v___x_486_: *mut lean_object = core::ptr::null_mut(); let mut v___x_487_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_485_, 1);
v___x_486_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_487_ = l_IO_println___at___00main_spec__1(v___x_486_);
if lean_obj_tag(v___x_487_) == 0 {
let mut v___x_488_: usize = 0; let mut v___x_489_: *mut lean_object = core::ptr::null_mut(); let mut v___x_490_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_487_, 1);
v___x_488_ = 0usize;
v___x_489_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__14), core::ptr::addr_of_mut!(l_main___closed__14_once), _init_l_main___closed__14);
v___x_490_ = l_IO_println___at___00main_spec__1(v___x_489_);
if lean_obj_tag(v___x_490_) == 0 {
let mut v___x_491_: *mut lean_object = core::ptr::null_mut(); let mut v___x_492_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_490_, 1);
v___x_491_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__16), core::ptr::addr_of_mut!(l_main___closed__16_once), _init_l_main___closed__16);
v___x_492_ = l_IO_println___at___00main_spec__1(v___x_491_);
if lean_obj_tag(v___x_492_) == 0 {
let mut v___x_493_: *mut lean_object = core::ptr::null_mut(); let mut v___x_494_: *mut lean_object = core::ptr::null_mut(); let mut v___x_495_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_492_, 1);
v___x_493_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
v___x_494_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__20), core::ptr::addr_of_mut!(l_main___closed__20_once), _init_l_main___closed__20);
v___x_495_ = l_IO_println___at___00main_spec__1(v___x_494_);
if lean_obj_tag(v___x_495_) == 0 {
let mut v___x_496_: *mut lean_object = core::ptr::null_mut(); let mut v___x_497_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_495_, 1);
v___x_496_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__24), core::ptr::addr_of_mut!(l_main___closed__24_once), _init_l_main___closed__24);
v___x_497_ = l_IO_println___at___00main_spec__1(v___x_496_);
if lean_obj_tag(v___x_497_) == 0 {
let mut v___x_498_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_497_, 1);
v___x_498_ = l_IO_println___at___00main_spec__3(v___x_493_);
if lean_obj_tag(v___x_498_) == 0 {
let mut v___x_499_: *mut lean_object = core::ptr::null_mut(); let mut v___x_500_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_498_, 1);
v___x_499_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__29), core::ptr::addr_of_mut!(l_main___closed__29_once), _init_l_main___closed__29);
v___x_500_ = l_IO_println___at___00main_spec__6(v___x_499_);
if lean_obj_tag(v___x_500_) == 0 {
let mut v___x_501_: *mut lean_object = core::ptr::null_mut(); let mut v___x_502_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_500_, 1);
v___x_501_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__30), core::ptr::addr_of_mut!(l_main___closed__30_once), _init_l_main___closed__30);
v___x_502_ = l_IO_println___at___00main_spec__3(v___x_501_);
if lean_obj_tag(v___x_502_) == 0 {
let mut v___x_503_: *mut lean_object = core::ptr::null_mut(); let mut v___x_504_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_502_, 1);
v___x_503_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__31), core::ptr::addr_of_mut!(l_main___closed__31_once), _init_l_main___closed__31);
v___x_504_ = l_IO_println___at___00main_spec__3(v___x_503_);
if lean_obj_tag(v___x_504_) == 0 {
let mut v___x_505_: *mut lean_object = core::ptr::null_mut(); let mut v___x_506_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_504_, 1);
v___x_505_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__32), core::ptr::addr_of_mut!(l_main___closed__32_once), _init_l_main___closed__32);
v___x_506_ = l_IO_println___at___00main_spec__3(v___x_505_);
if lean_obj_tag(v___x_506_) == 0 {
let mut v___x_507_: *mut lean_object = core::ptr::null_mut(); let mut v___x_508_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_506_, 1);
v___x_507_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__33), core::ptr::addr_of_mut!(l_main___closed__33_once), _init_l_main___closed__33);
v___x_508_ = l_IO_println___at___00main_spec__3(v___x_507_);
if lean_obj_tag(v___x_508_) == 0 {
let mut v___x_509_: *mut lean_object = core::ptr::null_mut(); let mut v___x_510_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_508_, 1);
v___x_509_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__34), core::ptr::addr_of_mut!(l_main___closed__34_once), _init_l_main___closed__34);
v___x_510_ = l_IO_println___at___00main_spec__3(v___x_509_);
if lean_obj_tag(v___x_510_) == 0 {
let mut v___x_511_: *mut lean_object = core::ptr::null_mut(); let mut v___x_512_: *mut lean_object = core::ptr::null_mut(); let mut v___x_513_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_510_, 1);
v___x_511_ = l_main___closed__35;
v___x_512_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__36), core::ptr::addr_of_mut!(l_main___closed__36_once), _init_l_main___closed__36);
v___x_513_ = l_IO_println___at___00main_spec__3(v___x_512_);
if lean_obj_tag(v___x_513_) == 0 {
let mut v___x_514_: *mut lean_object = core::ptr::null_mut(); let mut v___x_515_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_513_, 1);
v___x_514_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__38), core::ptr::addr_of_mut!(l_main___closed__38_once), _init_l_main___closed__38);
v___x_515_ = l_IO_println___at___00main_spec__3(v___x_514_);
if lean_obj_tag(v___x_515_) == 0 {
let mut v___y_517_: *mut lean_object = core::ptr::null_mut(); let mut v___y_532_: *mut lean_object = core::ptr::null_mut(); let mut v___y_547_: *mut lean_object = core::ptr::null_mut(); let mut v___y_562_: *mut lean_object = core::ptr::null_mut(); let mut v___y_563_: *mut lean_object = core::ptr::null_mut(); let mut v___y_564_: *mut lean_object = core::ptr::null_mut(); let mut v___y_581_: *mut lean_object = core::ptr::null_mut(); let mut v___x_597_: u8 = 0; 
lean_dec_ref_known(v___x_515_, 1);
v___x_597_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__40), core::ptr::addr_of_mut!(l_main___closed__40_once), _init_l_main___closed__40);
if v___x_597_ == 0 {
v___y_581_ = v___x_511_;
state = 18; continue;
} else {
let mut v___x_598_: u8 = 0; 
v___x_598_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__41), core::ptr::addr_of_mut!(l_main___closed__41_once), _init_l_main___closed__41);
if v___x_598_ == 0 {
if v___x_597_ == 0 {
v___y_581_ = v___x_511_;
state = 18; continue;
} else {
let mut v___x_599_: *mut lean_object = core::ptr::null_mut(); 
v___x_599_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__52), core::ptr::addr_of_mut!(l_main___closed__52_once), _init_l_main___closed__52);
v___y_581_ = v___x_599_;
state = 18; continue;
}
} else {
let mut v___x_600_: *mut lean_object = core::ptr::null_mut(); 
v___x_600_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__52), core::ptr::addr_of_mut!(l_main___closed__52_once), _init_l_main___closed__52);
v___y_581_ = v___x_600_;
state = 18; continue;
}
}
} else {
let mut v_a_601_: *mut lean_object = core::ptr::null_mut(); let mut v___x_603_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_604_: u8 = 0; let mut v_isSharedCheck_608_: u8 = 0; 
v_a_601_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_608_ = (!lean_is_exclusive(v___x_515_)) as u8;
if v_isSharedCheck_608_ == 0 {
v___x_603_ = v___x_515_;
v_isShared_604_ = v_isSharedCheck_608_;
state = 21; continue;
} else {
lean_inc(v_a_601_);
lean_dec(v___x_515_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
state = 21; continue;
}
}
} else {
let mut v_a_609_: *mut lean_object = core::ptr::null_mut(); let mut v___x_611_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_612_: u8 = 0; let mut v_isSharedCheck_616_: u8 = 0; 
v_a_609_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_616_ = (!lean_is_exclusive(v___x_513_)) as u8;
if v_isSharedCheck_616_ == 0 {
v___x_611_ = v___x_513_;
v_isShared_612_ = v_isSharedCheck_616_;
state = 23; continue;
} else {
lean_inc(v_a_609_);
lean_dec(v___x_513_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
state = 23; continue;
}
}
} else {
let mut v_a_617_: *mut lean_object = core::ptr::null_mut(); let mut v___x_619_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_620_: u8 = 0; let mut v_isSharedCheck_624_: u8 = 0; 
v_a_617_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_624_ = (!lean_is_exclusive(v___x_510_)) as u8;
if v_isSharedCheck_624_ == 0 {
v___x_619_ = v___x_510_;
v_isShared_620_ = v_isSharedCheck_624_;
state = 25; continue;
} else {
lean_inc(v_a_617_);
lean_dec(v___x_510_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
state = 25; continue;
}
}
} else {
let mut v_a_625_: *mut lean_object = core::ptr::null_mut(); let mut v___x_627_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_628_: u8 = 0; let mut v_isSharedCheck_632_: u8 = 0; 
v_a_625_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_632_ = (!lean_is_exclusive(v___x_508_)) as u8;
if v_isSharedCheck_632_ == 0 {
v___x_627_ = v___x_508_;
v_isShared_628_ = v_isSharedCheck_632_;
state = 27; continue;
} else {
lean_inc(v_a_625_);
lean_dec(v___x_508_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
state = 27; continue;
}
}
} else {
let mut v_a_633_: *mut lean_object = core::ptr::null_mut(); let mut v___x_635_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_636_: u8 = 0; let mut v_isSharedCheck_640_: u8 = 0; 
v_a_633_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_640_ = (!lean_is_exclusive(v___x_506_)) as u8;
if v_isSharedCheck_640_ == 0 {
v___x_635_ = v___x_506_;
v_isShared_636_ = v_isSharedCheck_640_;
state = 29; continue;
} else {
lean_inc(v_a_633_);
lean_dec(v___x_506_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
state = 29; continue;
}
}
} else {
let mut v_a_641_: *mut lean_object = core::ptr::null_mut(); let mut v___x_643_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_644_: u8 = 0; let mut v_isSharedCheck_648_: u8 = 0; 
v_a_641_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_648_ = (!lean_is_exclusive(v___x_504_)) as u8;
if v_isSharedCheck_648_ == 0 {
v___x_643_ = v___x_504_;
v_isShared_644_ = v_isSharedCheck_648_;
state = 31; continue;
} else {
lean_inc(v_a_641_);
lean_dec(v___x_504_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
state = 31; continue;
}
}
} else {
let mut v_a_649_: *mut lean_object = core::ptr::null_mut(); let mut v___x_651_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_652_: u8 = 0; let mut v_isSharedCheck_656_: u8 = 0; 
v_a_649_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_656_ = (!lean_is_exclusive(v___x_502_)) as u8;
if v_isSharedCheck_656_ == 0 {
v___x_651_ = v___x_502_;
v_isShared_652_ = v_isSharedCheck_656_;
state = 33; continue;
} else {
lean_inc(v_a_649_);
lean_dec(v___x_502_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
state = 33; continue;
}
}
} else {
let mut v_a_657_: *mut lean_object = core::ptr::null_mut(); let mut v___x_659_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_660_: u8 = 0; let mut v_isSharedCheck_664_: u8 = 0; 
v_a_657_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_664_ = (!lean_is_exclusive(v___x_500_)) as u8;
if v_isSharedCheck_664_ == 0 {
v___x_659_ = v___x_500_;
v_isShared_660_ = v_isSharedCheck_664_;
state = 35; continue;
} else {
lean_inc(v_a_657_);
lean_dec(v___x_500_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
state = 35; continue;
}
}
} else {
let mut v_a_665_: *mut lean_object = core::ptr::null_mut(); let mut v___x_667_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_668_: u8 = 0; let mut v_isSharedCheck_672_: u8 = 0; 
v_a_665_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_672_ = (!lean_is_exclusive(v___x_498_)) as u8;
if v_isSharedCheck_672_ == 0 {
v___x_667_ = v___x_498_;
v_isShared_668_ = v_isSharedCheck_672_;
state = 37; continue;
} else {
lean_inc(v_a_665_);
lean_dec(v___x_498_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
state = 37; continue;
}
}
} else {
let mut v_a_673_: *mut lean_object = core::ptr::null_mut(); let mut v___x_675_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_676_: u8 = 0; let mut v_isSharedCheck_680_: u8 = 0; 
v_a_673_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_680_ = (!lean_is_exclusive(v___x_497_)) as u8;
if v_isSharedCheck_680_ == 0 {
v___x_675_ = v___x_497_;
v_isShared_676_ = v_isSharedCheck_680_;
state = 39; continue;
} else {
lean_inc(v_a_673_);
lean_dec(v___x_497_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
state = 39; continue;
}
}
} else {
let mut v_a_681_: *mut lean_object = core::ptr::null_mut(); let mut v___x_683_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_684_: u8 = 0; let mut v_isSharedCheck_688_: u8 = 0; 
v_a_681_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_688_ = (!lean_is_exclusive(v___x_495_)) as u8;
if v_isSharedCheck_688_ == 0 {
v___x_683_ = v___x_495_;
v_isShared_684_ = v_isSharedCheck_688_;
state = 41; continue;
} else {
lean_inc(v_a_681_);
lean_dec(v___x_495_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
state = 41; continue;
}
}
} else {
let mut v_a_689_: *mut lean_object = core::ptr::null_mut(); let mut v___x_691_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_692_: u8 = 0; let mut v_isSharedCheck_696_: u8 = 0; 
v_a_689_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_696_ = (!lean_is_exclusive(v___x_492_)) as u8;
if v_isSharedCheck_696_ == 0 {
v___x_691_ = v___x_492_;
v_isShared_692_ = v_isSharedCheck_696_;
state = 43; continue;
} else {
lean_inc(v_a_689_);
lean_dec(v___x_492_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
state = 43; continue;
}
}
} else {
let mut v_a_697_: *mut lean_object = core::ptr::null_mut(); let mut v___x_699_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_700_: u8 = 0; let mut v_isSharedCheck_704_: u8 = 0; 
v_a_697_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_704_ = (!lean_is_exclusive(v___x_490_)) as u8;
if v_isSharedCheck_704_ == 0 {
v___x_699_ = v___x_490_;
v_isShared_700_ = v_isSharedCheck_704_;
state = 45; continue;
} else {
lean_inc(v_a_697_);
lean_dec(v___x_490_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
state = 45; continue;
}
}
} else {
let mut v_a_705_: *mut lean_object = core::ptr::null_mut(); let mut v___x_707_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_708_: u8 = 0; let mut v_isSharedCheck_712_: u8 = 0; 
v_a_705_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_712_ = (!lean_is_exclusive(v___x_487_)) as u8;
if v_isSharedCheck_712_ == 0 {
v___x_707_ = v___x_487_;
v_isShared_708_ = v_isSharedCheck_712_;
state = 47; continue;
} else {
lean_inc(v_a_705_);
lean_dec(v___x_487_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
state = 47; continue;
}
}
} else {
let mut v_a_713_: *mut lean_object = core::ptr::null_mut(); let mut v___x_715_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_716_: u8 = 0; let mut v_isSharedCheck_720_: u8 = 0; 
v_a_713_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_720_ = (!lean_is_exclusive(v___x_485_)) as u8;
if v_isSharedCheck_720_ == 0 {
v___x_715_ = v___x_485_;
v_isShared_716_ = v_isSharedCheck_720_;
state = 49; continue;
} else {
lean_inc(v_a_713_);
lean_dec(v___x_485_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
state = 49; continue;
}
}
} else {
let mut v_a_721_: *mut lean_object = core::ptr::null_mut(); let mut v___x_723_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_724_: u8 = 0; let mut v_isSharedCheck_728_: u8 = 0; 
v_a_721_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_728_ = (!lean_is_exclusive(v___x_483_)) as u8;
if v_isSharedCheck_728_ == 0 {
v___x_723_ = v___x_483_;
v_isShared_724_ = v_isSharedCheck_728_;
state = 51; continue;
} else {
lean_inc(v_a_721_);
lean_dec(v___x_483_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
state = 51; continue;
}
}
}
1 => {
v___x_463_ = l_IO_println___at___00main_spec__3(v___y_462_);
if lean_obj_tag(v___x_463_) == 0 {
let mut v___x_465_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_466_: u8 = 0; let mut v_isSharedCheck_471_: u8 = 0; 
v_isSharedCheck_471_ = (!lean_is_exclusive(v___x_463_)) as u8;
if v_isSharedCheck_471_ == 0 {
let mut v_unused_472_: *mut lean_object = core::ptr::null_mut(); 
v_unused_472_ = lean_ctor_get(v___x_463_, 0);
lean_dec(v_unused_472_);
v___x_465_ = v___x_463_;
v_isShared_466_ = v_isSharedCheck_471_;
state = 2; continue;
} else {
lean_dec(v___x_463_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_471_;
state = 2; continue;
}
} else {
let mut v_a_473_: *mut lean_object = core::ptr::null_mut(); let mut v___x_475_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_476_: u8 = 0; let mut v_isSharedCheck_480_: u8 = 0; 
v_a_473_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_480_ = (!lean_is_exclusive(v___x_463_)) as u8;
if v_isSharedCheck_480_ == 0 {
v___x_475_ = v___x_463_;
v_isShared_476_ = v_isSharedCheck_480_;
state = 4; continue;
} else {
lean_inc(v_a_473_);
lean_dec(v___x_463_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
state = 4; continue;
}
}
}
6 => {
v___x_518_ = l_IO_println___at___00main_spec__3(v___y_517_);
if lean_obj_tag(v___x_518_) == 0 {
let mut v___x_519_: u8 = 0; 
lean_dec_ref_known(v___x_518_, 1);
v___x_519_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__40), core::ptr::addr_of_mut!(l_main___closed__40_once), _init_l_main___closed__40);
if v___x_519_ == 0 {
v___y_462_ = v___x_511_;
state = 1; continue;
} else {
let mut v___x_520_: u8 = 0; 
v___x_520_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__41), core::ptr::addr_of_mut!(l_main___closed__41_once), _init_l_main___closed__41);
if v___x_520_ == 0 {
if v___x_519_ == 0 {
v___y_462_ = v___x_511_;
state = 1; continue;
} else {
let mut v___x_521_: *mut lean_object = core::ptr::null_mut(); 
v___x_521_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__43), core::ptr::addr_of_mut!(l_main___closed__43_once), _init_l_main___closed__43);
v___y_462_ = v___x_521_;
state = 1; continue;
}
} else {
let mut v___x_522_: *mut lean_object = core::ptr::null_mut(); 
v___x_522_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__43), core::ptr::addr_of_mut!(l_main___closed__43_once), _init_l_main___closed__43);
v___y_462_ = v___x_522_;
state = 1; continue;
}
}
} else {
let mut v_a_523_: *mut lean_object = core::ptr::null_mut(); let mut v___x_525_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_526_: u8 = 0; let mut v_isSharedCheck_530_: u8 = 0; 
v_a_523_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_530_ = (!lean_is_exclusive(v___x_518_)) as u8;
if v_isSharedCheck_530_ == 0 {
v___x_525_ = v___x_518_;
v_isShared_526_ = v_isSharedCheck_530_;
state = 7; continue;
} else {
lean_inc(v_a_523_);
lean_dec(v___x_518_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
state = 7; continue;
}
}
}
9 => {
v___x_533_ = l_IO_println___at___00main_spec__3(v___y_532_);
if lean_obj_tag(v___x_533_) == 0 {
let mut v___x_534_: u8 = 0; 
lean_dec_ref_known(v___x_533_, 1);
v___x_534_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__40), core::ptr::addr_of_mut!(l_main___closed__40_once), _init_l_main___closed__40);
if v___x_534_ == 0 {
v___y_517_ = v___x_511_;
state = 6; continue;
} else {
let mut v___x_535_: u8 = 0; 
v___x_535_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__41), core::ptr::addr_of_mut!(l_main___closed__41_once), _init_l_main___closed__41);
if v___x_535_ == 0 {
if v___x_534_ == 0 {
v___y_517_ = v___x_511_;
state = 6; continue;
} else {
let mut v___x_536_: *mut lean_object = core::ptr::null_mut(); 
v___x_536_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__44), core::ptr::addr_of_mut!(l_main___closed__44_once), _init_l_main___closed__44);
v___y_517_ = v___x_536_;
state = 6; continue;
}
} else {
let mut v___x_537_: *mut lean_object = core::ptr::null_mut(); 
v___x_537_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__44), core::ptr::addr_of_mut!(l_main___closed__44_once), _init_l_main___closed__44);
v___y_517_ = v___x_537_;
state = 6; continue;
}
}
} else {
let mut v_a_538_: *mut lean_object = core::ptr::null_mut(); let mut v___x_540_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_541_: u8 = 0; let mut v_isSharedCheck_545_: u8 = 0; 
v_a_538_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_545_ = (!lean_is_exclusive(v___x_533_)) as u8;
if v_isSharedCheck_545_ == 0 {
v___x_540_ = v___x_533_;
v_isShared_541_ = v_isSharedCheck_545_;
state = 10; continue;
} else {
lean_inc(v_a_538_);
lean_dec(v___x_533_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
state = 10; continue;
}
}
}
12 => {
v___x_548_ = l_IO_println___at___00main_spec__3(v___y_547_);
if lean_obj_tag(v___x_548_) == 0 {
let mut v___x_549_: u8 = 0; 
lean_dec_ref_known(v___x_548_, 1);
v___x_549_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__40), core::ptr::addr_of_mut!(l_main___closed__40_once), _init_l_main___closed__40);
if v___x_549_ == 0 {
v___y_532_ = v___x_511_;
state = 9; continue;
} else {
let mut v___x_550_: u8 = 0; 
v___x_550_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__41), core::ptr::addr_of_mut!(l_main___closed__41_once), _init_l_main___closed__41);
if v___x_550_ == 0 {
if v___x_549_ == 0 {
v___y_532_ = v___x_511_;
state = 9; continue;
} else {
let mut v___x_551_: *mut lean_object = core::ptr::null_mut(); 
v___x_551_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__45), core::ptr::addr_of_mut!(l_main___closed__45_once), _init_l_main___closed__45);
v___y_532_ = v___x_551_;
state = 9; continue;
}
} else {
let mut v___x_552_: *mut lean_object = core::ptr::null_mut(); 
v___x_552_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__45), core::ptr::addr_of_mut!(l_main___closed__45_once), _init_l_main___closed__45);
v___y_532_ = v___x_552_;
state = 9; continue;
}
}
} else {
let mut v_a_553_: *mut lean_object = core::ptr::null_mut(); let mut v___x_555_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_556_: u8 = 0; let mut v_isSharedCheck_560_: u8 = 0; 
v_a_553_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_560_ = (!lean_is_exclusive(v___x_548_)) as u8;
if v_isSharedCheck_560_ == 0 {
v___x_555_ = v___x_548_;
v_isShared_556_ = v_isSharedCheck_560_;
state = 13; continue;
} else {
lean_inc(v_a_553_);
lean_dec(v___x_548_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
state = 13; continue;
}
}
}
15 => {
v___x_565_ = l_IO_println___at___00main_spec__3(v___y_564_);
if lean_obj_tag(v___x_565_) == 0 {
let mut v___x_566_: u8 = 0; 
lean_dec_ref_known(v___x_565_, 1);
v___x_566_ = lean_nat_dec_lt(v___x_481_, v___y_563_);
if v___x_566_ == 0 {
v___y_547_ = v___x_511_;
state = 12; continue;
} else {
let mut v___x_567_: u8 = 0; 
v___x_567_ = lean_nat_dec_le(v___y_563_, v___y_563_);
if v___x_567_ == 0 {
if v___x_566_ == 0 {
v___y_547_ = v___x_511_;
state = 12; continue;
} else {
let mut v___x_568_: usize = 0; let mut v___x_569_: *mut lean_object = core::ptr::null_mut(); 
v___x_568_ = lean_usize_of_nat(v___y_563_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__10(v___y_562_, v___x_488_, v___x_568_, v___x_511_);
v___y_547_ = v___x_569_;
state = 12; continue;
}
} else {
let mut v___x_570_: usize = 0; let mut v___x_571_: *mut lean_object = core::ptr::null_mut(); 
v___x_570_ = lean_usize_of_nat(v___y_563_);
v___x_571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__10(v___y_562_, v___x_488_, v___x_570_, v___x_511_);
v___y_547_ = v___x_571_;
state = 12; continue;
}
}
} else {
let mut v_a_572_: *mut lean_object = core::ptr::null_mut(); let mut v___x_574_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_575_: u8 = 0; let mut v_isSharedCheck_579_: u8 = 0; 
v_a_572_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_579_ = (!lean_is_exclusive(v___x_565_)) as u8;
if v_isSharedCheck_579_ == 0 {
v___x_574_ = v___x_565_;
v_isShared_575_ = v_isSharedCheck_579_;
state = 16; continue;
} else {
lean_inc(v_a_572_);
lean_dec(v___x_565_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
state = 16; continue;
}
}
}
18 => {
v___x_582_ = l_IO_println___at___00main_spec__3(v___y_581_);
if lean_obj_tag(v___x_582_) == 0 {
let mut v___x_583_: *mut lean_object = core::ptr::null_mut(); let mut v___x_584_: *mut lean_object = core::ptr::null_mut(); let mut v___x_585_: u8 = 0; 
lean_dec_ref_known(v___x_582_, 1);
v___x_583_ = l_main___closed__46;
v___x_584_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__47), core::ptr::addr_of_mut!(l_main___closed__47_once), _init_l_main___closed__47);
v___x_585_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__48), core::ptr::addr_of_mut!(l_main___closed__48_once), _init_l_main___closed__48);
if v___x_585_ == 0 {
v___y_562_ = v___x_583_;
v___y_563_ = v___x_584_;
v___y_564_ = v___x_511_;
state = 15; continue;
} else {
let mut v___x_586_: u8 = 0; 
v___x_586_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__49), core::ptr::addr_of_mut!(l_main___closed__49_once), _init_l_main___closed__49);
if v___x_586_ == 0 {
if v___x_585_ == 0 {
v___y_562_ = v___x_583_;
v___y_563_ = v___x_584_;
v___y_564_ = v___x_511_;
state = 15; continue;
} else {
let mut v___x_587_: *mut lean_object = core::ptr::null_mut(); 
v___x_587_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__51), core::ptr::addr_of_mut!(l_main___closed__51_once), _init_l_main___closed__51);
v___y_562_ = v___x_583_;
v___y_563_ = v___x_584_;
v___y_564_ = v___x_587_;
state = 15; continue;
}
} else {
let mut v___x_588_: *mut lean_object = core::ptr::null_mut(); 
v___x_588_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__51), core::ptr::addr_of_mut!(l_main___closed__51_once), _init_l_main___closed__51);
v___y_562_ = v___x_583_;
v___y_563_ = v___x_584_;
v___y_564_ = v___x_588_;
state = 15; continue;
}
}
} else {
let mut v_a_589_: *mut lean_object = core::ptr::null_mut(); let mut v___x_591_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_592_: u8 = 0; let mut v_isSharedCheck_596_: u8 = 0; 
v_a_589_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_596_ = (!lean_is_exclusive(v___x_582_)) as u8;
if v_isSharedCheck_596_ == 0 {
v___x_591_ = v___x_582_;
v_isShared_592_ = v_isSharedCheck_596_;
state = 19; continue;
} else {
lean_inc(v_a_589_);
lean_dec(v___x_582_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
state = 19; continue;
}
}
}
21 => {
if v_isShared_604_ == 0 {
v___x_606_ = v___x_603_;
state = 22; continue;
} else {
let mut v_reuseFailAlloc_607_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
state = 22; continue;
}
}
23 => {
if v_isShared_612_ == 0 {
v___x_614_ = v___x_611_;
state = 24; continue;
} else {
let mut v_reuseFailAlloc_615_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
state = 24; continue;
}
}
25 => {
if v_isShared_620_ == 0 {
v___x_622_ = v___x_619_;
state = 26; continue;
} else {
let mut v_reuseFailAlloc_623_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
state = 26; continue;
}
}
27 => {
if v_isShared_628_ == 0 {
v___x_630_ = v___x_627_;
state = 28; continue;
} else {
let mut v_reuseFailAlloc_631_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
state = 28; continue;
}
}
29 => {
if v_isShared_636_ == 0 {
v___x_638_ = v___x_635_;
state = 30; continue;
} else {
let mut v_reuseFailAlloc_639_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
state = 30; continue;
}
}
31 => {
if v_isShared_644_ == 0 {
v___x_646_ = v___x_643_;
state = 32; continue;
} else {
let mut v_reuseFailAlloc_647_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
state = 32; continue;
}
}
33 => {
if v_isShared_652_ == 0 {
v___x_654_ = v___x_651_;
state = 34; continue;
} else {
let mut v_reuseFailAlloc_655_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
state = 34; continue;
}
}
35 => {
if v_isShared_660_ == 0 {
v___x_662_ = v___x_659_;
state = 36; continue;
} else {
let mut v_reuseFailAlloc_663_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
state = 36; continue;
}
}
37 => {
if v_isShared_668_ == 0 {
v___x_670_ = v___x_667_;
state = 38; continue;
} else {
let mut v_reuseFailAlloc_671_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
state = 38; continue;
}
}
39 => {
if v_isShared_676_ == 0 {
v___x_678_ = v___x_675_;
state = 40; continue;
} else {
let mut v_reuseFailAlloc_679_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
state = 40; continue;
}
}
41 => {
if v_isShared_684_ == 0 {
v___x_686_ = v___x_683_;
state = 42; continue;
} else {
let mut v_reuseFailAlloc_687_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
state = 42; continue;
}
}
43 => {
if v_isShared_692_ == 0 {
v___x_694_ = v___x_691_;
state = 44; continue;
} else {
let mut v_reuseFailAlloc_695_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
state = 44; continue;
}
}
45 => {
if v_isShared_700_ == 0 {
v___x_702_ = v___x_699_;
state = 46; continue;
} else {
let mut v_reuseFailAlloc_703_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
state = 46; continue;
}
}
47 => {
if v_isShared_708_ == 0 {
v___x_710_ = v___x_707_;
state = 48; continue;
} else {
let mut v_reuseFailAlloc_711_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
state = 48; continue;
}
}
49 => {
if v_isShared_716_ == 0 {
v___x_718_ = v___x_715_;
state = 50; continue;
} else {
let mut v_reuseFailAlloc_719_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
state = 50; continue;
}
}
51 => {
if v_isShared_724_ == 0 {
v___x_726_ = v___x_723_;
state = 52; continue;
} else {
let mut v_reuseFailAlloc_727_: *mut lean_object = core::ptr::null_mut(); 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
state = 52; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_729_: *mut lean_object) -> *mut lean_object{
let mut v_res_730_: *mut lean_object = core::ptr::null_mut(); 
v_res_730_ = _lean_main();
return v_res_730_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_array__test(builtin: u8) -> *mut lean_object {
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
  let res = initialize_array__test(1 /* builtin */);
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

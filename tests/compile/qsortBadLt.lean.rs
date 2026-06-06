// Lean compiler output
// Module: qsortBadLt
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_array_fswap(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fget_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fget(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_le(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_nat_shiftr(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_to_list(_: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_IO_println___at___00main_spec__1___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [35, 0]};
static mut l_IO_println___at___00main_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_array_object<2> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*2) as u16, m_other: 0, m_tag: 246 }, m_size: 2, m_capacity: 2, m_data: [((( 1 as usize) << 1) | 1) as *mut lean_object,((( 2 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: u8 = 0;
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: u8 = 0;
#[no_mangle] pub unsafe extern "C" fn l_badLt(mut v_a_1_: *mut lean_object, mut v_b_2_: *mut lean_object) -> u8{
let mut v___x_3_: u8 = 0; 
v___x_3_ = lean_nat_dec_eq(v_a_1_, v_b_2_);
if v___x_3_ == 0 {
let mut v___x_4_: u8 = 0; 
v___x_4_ = 1;
return v___x_4_;
} else {
let mut v___x_5_: u8 = 0; 
v___x_5_ = 0;
return v___x_5_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_badLt___boxed(mut v_a_6_: *mut lean_object, mut v_b_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: u8 = 0; let mut v_r_9_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_badLt(v_a_6_, v_b_7_);
lean_dec(v_b_7_);
lean_dec(v_a_6_);
v_r_9_ = lean_box((v_res_8_) as usize);
return v_r_9_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(mut v_s_10_: *mut lean_object) -> *mut lean_object{
let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_13_: *mut lean_object = core::ptr::null_mut(); let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); 
v___x_12_ = lean_get_stdout();
v_putStr_13_ = lean_ctor_get(v___x_12_, 4);
lean_inc_ref(v_putStr_13_);
lean_dec_ref(v___x_12_);
v___x_14_ = lean_apply_2(v_putStr_13_, v_s_10_, lean_box(0));
return v___x_14_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__1_spec__3___boxed(mut v_s_15_: *mut lean_object, mut v_a_16_: *mut lean_object) -> *mut lean_object{
let mut v_res_17_: *mut lean_object = core::ptr::null_mut(); 
v_res_17_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(v_s_15_);
return v_res_17_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3(mut v_x_19_: *mut lean_object, mut v_x_20_: *mut lean_object) -> *mut lean_object{
let mut v_head_21_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_20_) == 0 {
return v_x_19_;
} else {
let mut v_head_21_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); 
v_head_21_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_head_21_);
v_tail_22_ = lean_ctor_get(v_x_20_, 1);
lean_inc(v_tail_22_);
lean_dec_ref_known(v_x_20_, 2);
v___x_23_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3___closed__0;
v___x_24_ = lean_string_append(v_x_19_, v___x_23_);
v___x_25_ = l_Nat_reprFast(v_head_21_);
v___x_26_ = lean_string_append(v___x_24_, v___x_25_);
lean_dec_ref(v___x_25_);
v_x_19_ = v___x_26_;
v_x_20_ = v_tail_22_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00main_spec__1_spec__2(mut v_x_31_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_31_) == 0 {
let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); 
v___x_32_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__0;
return v___x_32_;
} else {
let mut v_tail_33_: *mut lean_object = core::ptr::null_mut(); 
v_tail_33_ = lean_ctor_get(v_x_31_, 1);
if lean_obj_tag(v_tail_33_) == 0 {
let mut v_head_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); 
v_head_34_ = lean_ctor_get(v_x_31_, 0);
lean_inc(v_head_34_);
lean_dec_ref_known(v_x_31_, 2);
v___x_35_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1;
v___x_36_ = l_Nat_reprFast(v_head_34_);
v___x_37_ = lean_string_append(v___x_35_, v___x_36_);
lean_dec_ref(v___x_36_);
v___x_38_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__2;
v___x_39_ = lean_string_append(v___x_37_, v___x_38_);
return v___x_39_;
} else {
let mut v_head_40_: *mut lean_object = core::ptr::null_mut(); let mut v___x_41_: *mut lean_object = core::ptr::null_mut(); let mut v___x_42_: *mut lean_object = core::ptr::null_mut(); let mut v___x_43_: *mut lean_object = core::ptr::null_mut(); let mut v___x_44_: *mut lean_object = core::ptr::null_mut(); let mut v___x_45_: u32 = 0; let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_tail_33_);
v_head_40_ = lean_ctor_get(v_x_31_, 0);
lean_inc(v_head_40_);
lean_dec_ref_known(v_x_31_, 2);
v___x_41_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2___closed__1;
v___x_42_ = l_Nat_reprFast(v_head_40_);
v___x_43_ = lean_string_append(v___x_41_, v___x_42_);
lean_dec_ref(v___x_42_);
v___x_44_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__2_spec__3(v___x_43_, v_tail_33_);
v___x_45_ = 93;
v___x_46_ = lean_string_push(v___x_44_, v___x_45_);
return v___x_46_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_48_: *mut lean_object) -> *mut lean_object{
let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: u32 = 0; let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); 
v___x_50_ = l_IO_println___at___00main_spec__1___closed__0;
v___x_51_ = lean_array_to_list(v_s_48_);
v___x_52_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__2(v___x_51_);
v___x_53_ = lean_string_append(v___x_50_, v___x_52_);
lean_dec_ref(v___x_52_);
v___x_54_ = 10;
v___x_55_ = lean_string_push(v___x_53_, v___x_54_);
v___x_56_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__3(v___x_55_);
return v___x_56_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_57_: *mut lean_object, mut v_a_58_: *mut lean_object) -> *mut lean_object{
let mut v_res_59_: *mut lean_object = core::ptr::null_mut(); 
v_res_59_ = l_IO_println___at___00main_spec__1(v_s_57_);
return v_res_59_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0_spec__0___redArg(mut v_hi_60_: *mut lean_object, mut v_pivot_61_: *mut lean_object, mut v_as_62_: *mut lean_object, mut v_i_63_: *mut lean_object, mut v_k_64_: *mut lean_object) -> *mut lean_object{
let mut v___x_65_: u8 = 0; let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: u8 = 0; let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_65_ = lean_nat_dec_lt(v_k_64_, v_hi_60_);
if v___x_65_ == 0 {
let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
lean_dec(v_k_64_);
v___x_66_ = lean_array_fswap(v_as_62_, v_i_63_, v_hi_60_);
v___x_67_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_67_, 0, v_i_63_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
return v___x_67_;
} else {
let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: u8 = 0; 
v___x_68_ = lean_array_fget_borrowed(v_as_62_, v_k_64_);
v___x_69_ = l_badLt(v___x_68_, v_pivot_61_);
if v___x_69_ == 0 {
let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); 
v___x_70_ = lean_unsigned_to_nat(1);
v___x_71_ = lean_nat_add(v_k_64_, v___x_70_);
lean_dec(v_k_64_);
v_k_64_ = v___x_71_;
state = 0; continue;
} else {
let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); 
v___x_73_ = lean_array_fswap(v_as_62_, v_i_63_, v_k_64_);
v___x_74_ = lean_unsigned_to_nat(1);
v___x_75_ = lean_nat_add(v_i_63_, v___x_74_);
lean_dec(v_i_63_);
v___x_76_ = lean_nat_add(v_k_64_, v___x_74_);
lean_dec(v_k_64_);
v_as_62_ = v___x_73_;
v_i_63_ = v___x_75_;
v_k_64_ = v___x_76_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0_spec__0___redArg___boxed(mut v_hi_78_: *mut lean_object, mut v_pivot_79_: *mut lean_object, mut v_as_80_: *mut lean_object, mut v_i_81_: *mut lean_object, mut v_k_82_: *mut lean_object) -> *mut lean_object{
let mut v_res_83_: *mut lean_object = core::ptr::null_mut(); 
v_res_83_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0_spec__0___redArg(v_hi_78_, v_pivot_79_, v_as_80_, v_i_81_, v_k_82_);
lean_dec(v_pivot_79_);
lean_dec(v_hi_78_);
return v_res_83_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0___redArg(mut v_n_84_: *mut lean_object, mut v_as_85_: *mut lean_object, mut v_lo_86_: *mut lean_object, mut v_hi_87_: *mut lean_object) -> *mut lean_object{
let mut v___y_89_: *mut lean_object = core::ptr::null_mut(); let mut v_pivot_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v_fst_92_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: u8 = 0; let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: u8 = 0; let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v_mid_102_: *mut lean_object = core::ptr::null_mut(); let mut v___y_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: u8 = 0; let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___y_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: u8 = 0; let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: u8 = 0; let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_99_ = lean_nat_dec_lt(v_lo_86_, v_hi_87_);
if v___x_99_ == 0 {
lean_dec(v_lo_86_);
return v_as_85_;
} else {
let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v_mid_102_: *mut lean_object = core::ptr::null_mut(); let mut v___y_104_: *mut lean_object = core::ptr::null_mut(); let mut v___y_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: u8 = 0; 
v___x_100_ = lean_nat_add(v_lo_86_, v_hi_87_);
v___x_101_ = lean_unsigned_to_nat(1);
v_mid_102_ = lean_nat_shiftr(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
v___x_115_ = lean_array_fget_borrowed(v_as_85_, v_mid_102_);
v___x_116_ = lean_array_fget_borrowed(v_as_85_, v_lo_86_);
v___x_117_ = l_badLt(v___x_115_, v___x_116_);
if v___x_117_ == 0 {
v___y_110_ = v_as_85_;
state = 3; continue;
} else {
let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); 
v___x_118_ = lean_array_fswap(v_as_85_, v_lo_86_, v_mid_102_);
v___y_110_ = v___x_118_;
state = 3; continue;
}
}
}
1 => {
v_pivot_90_ = lean_array_fget(v___y_89_, v_hi_87_);
lean_inc_n(v_lo_86_, 2);
v___x_91_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0_spec__0___redArg(v_hi_87_, v_pivot_90_, v___y_89_, v_lo_86_, v_lo_86_);
lean_dec(v_pivot_90_);
v_fst_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_fst_92_);
v_snd_93_ = lean_ctor_get(v___x_91_, 1);
lean_inc(v_snd_93_);
lean_dec_ref(v___x_91_);
v___x_94_ = lean_nat_dec_le(v_hi_87_, v_fst_92_);
if v___x_94_ == 0 {
let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); 
v___x_95_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0___redArg(v_n_84_, v_snd_93_, v_lo_86_, v_fst_92_);
v___x_96_ = lean_unsigned_to_nat(1);
v___x_97_ = lean_nat_add(v_fst_92_, v___x_96_);
lean_dec(v_fst_92_);
v_as_85_ = v___x_95_;
v_lo_86_ = v___x_97_;
state = 0; continue;
} else {
lean_dec(v_fst_92_);
lean_dec(v_lo_86_);
return v_snd_93_;
}
}
2 => {
v___x_105_ = lean_array_fget_borrowed(v___y_104_, v_mid_102_);
v___x_106_ = lean_array_fget_borrowed(v___y_104_, v_hi_87_);
v___x_107_ = l_badLt(v___x_105_, v___x_106_);
if v___x_107_ == 0 {
lean_dec(v_mid_102_);
v___y_89_ = v___y_104_;
state = 1; continue;
} else {
let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); 
v___x_108_ = lean_array_fswap(v___y_104_, v_mid_102_, v_hi_87_);
lean_dec(v_mid_102_);
v___y_89_ = v___x_108_;
state = 1; continue;
}
}
3 => {
v___x_111_ = lean_array_fget_borrowed(v___y_110_, v_hi_87_);
v___x_112_ = lean_array_fget_borrowed(v___y_110_, v_lo_86_);
v___x_113_ = l_badLt(v___x_111_, v___x_112_);
if v___x_113_ == 0 {
v___y_104_ = v___y_110_;
state = 2; continue;
} else {
let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); 
v___x_114_ = lean_array_fswap(v___y_110_, v_lo_86_, v_hi_87_);
v___y_104_ = v___x_114_;
state = 2; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0___redArg___boxed(mut v_n_119_: *mut lean_object, mut v_as_120_: *mut lean_object, mut v_lo_121_: *mut lean_object, mut v_hi_122_: *mut lean_object) -> *mut lean_object{
let mut v_res_123_: *mut lean_object = core::ptr::null_mut(); 
v_res_123_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0___redArg(v_n_119_, v_as_120_, v_lo_121_, v_hi_122_);
lean_dec(v_hi_122_);
lean_dec(v_n_119_);
return v_res_123_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v_xs_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); 
v_xs_129_ = l_main___closed__0;
v___x_130_ = lean_array_get_size(v_xs_129_);
return v___x_130_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> u8{
let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: *mut lean_object = core::ptr::null_mut(); let mut v___x_133_: u8 = 0; 
v___x_131_ = lean_unsigned_to_nat(0);
v___x_132_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_133_ = lean_nat_dec_eq(v___x_132_, v___x_131_);
return v___x_133_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> *mut lean_object{
let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); 
v___x_134_ = lean_unsigned_to_nat(1);
v___x_135_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_136_ = lean_nat_sub(v___x_135_, v___x_134_);
return v___x_136_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> u8{
let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: u8 = 0; 
v___x_137_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_138_ = lean_unsigned_to_nat(0);
v___x_139_ = lean_nat_dec_le(v___x_138_, v___x_137_);
return v___x_139_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v_xs_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___y_144_: *mut lean_object = core::ptr::null_mut(); let mut v___y_145_: *mut lean_object = core::ptr::null_mut(); let mut v___x_146_: *mut lean_object = core::ptr::null_mut(); let mut v___x_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: u8 = 0; let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___y_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_153_: u8 = 0; let mut v___x_154_: u8 = 0; let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_xs_141_ = l_main___closed__0;
v___x_142_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_148_ = lean_unsigned_to_nat(0);
v___x_149_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
if v___x_149_ == 0 {
let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v___y_152_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: u8 = 0; 
v___x_150_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_154_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
if v___x_154_ == 0 {
v___y_152_ = v___x_150_;
state = 2; continue;
} else {
v___y_152_ = v___x_148_;
state = 2; continue;
}
} else {
let mut v___x_155_: *mut lean_object = core::ptr::null_mut(); 
v___x_155_ = l_IO_println___at___00main_spec__1(v_xs_141_);
return v___x_155_;
}
}
1 => {
v___x_146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0___redArg(v___x_142_, v_xs_141_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
v___x_147_ = l_IO_println___at___00main_spec__1(v___x_146_);
return v___x_147_;
}
2 => {
v___x_153_ = lean_nat_dec_le(v___y_152_, v___x_150_);
if v___x_153_ == 0 {
lean_inc(v___y_152_);
v___y_144_ = v___y_152_;
v___y_145_ = v___y_152_;
state = 1; continue;
} else {
v___y_144_ = v___y_152_;
v___y_145_ = v___x_150_;
state = 1; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_156_: *mut lean_object) -> *mut lean_object{
let mut v_res_157_: *mut lean_object = core::ptr::null_mut(); 
v_res_157_ = _lean_main();
return v_res_157_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0(mut v_n_158_: *mut lean_object, mut v_as_159_: *mut lean_object, mut v_lo_160_: *mut lean_object, mut v_hi_161_: *mut lean_object, mut v_w_162_: *mut lean_object, mut v_hlo_163_: *mut lean_object, mut v_hhi_164_: *mut lean_object) -> *mut lean_object{
let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); 
v___x_165_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0___redArg(v_n_158_, v_as_159_, v_lo_160_, v_hi_161_);
return v___x_165_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0___boxed(mut v_n_166_: *mut lean_object, mut v_as_167_: *mut lean_object, mut v_lo_168_: *mut lean_object, mut v_hi_169_: *mut lean_object, mut v_w_170_: *mut lean_object, mut v_hlo_171_: *mut lean_object, mut v_hhi_172_: *mut lean_object) -> *mut lean_object{
let mut v_res_173_: *mut lean_object = core::ptr::null_mut(); 
v_res_173_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0(v_n_166_, v_as_167_, v_lo_168_, v_hi_169_, v_w_170_, v_hlo_171_, v_hhi_172_);
lean_dec(v_hi_169_);
lean_dec(v_n_166_);
return v_res_173_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0_spec__0(mut v_n_174_: *mut lean_object, mut v_lo_175_: *mut lean_object, mut v_hi_176_: *mut lean_object, mut v_hhi_177_: *mut lean_object, mut v_pivot_178_: *mut lean_object, mut v_as_179_: *mut lean_object, mut v_i_180_: *mut lean_object, mut v_k_181_: *mut lean_object, mut v_ilo_182_: *mut lean_object, mut v_ik_183_: *mut lean_object, mut v_w_184_: *mut lean_object) -> *mut lean_object{
let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); 
v___x_185_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0_spec__0___redArg(v_hi_176_, v_pivot_178_, v_as_179_, v_i_180_, v_k_181_);
return v___x_185_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0_spec__0___boxed(mut v_n_186_: *mut lean_object, mut v_lo_187_: *mut lean_object, mut v_hi_188_: *mut lean_object, mut v_hhi_189_: *mut lean_object, mut v_pivot_190_: *mut lean_object, mut v_as_191_: *mut lean_object, mut v_i_192_: *mut lean_object, mut v_k_193_: *mut lean_object, mut v_ilo_194_: *mut lean_object, mut v_ik_195_: *mut lean_object, mut v_w_196_: *mut lean_object) -> *mut lean_object{
let mut v_res_197_: *mut lean_object = core::ptr::null_mut(); 
v_res_197_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00main_spec__0_spec__0(v_n_186_, v_lo_187_, v_hi_188_, v_hhi_189_, v_pivot_190_, v_as_191_, v_i_192_, v_k_193_, v_ilo_194_, v_ik_195_, v_w_196_);
lean_dec(v_pivot_190_);
lean_dec(v_hi_188_);
lean_dec(v_lo_187_);
lean_dec(v_n_186_);
return v_res_197_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_qsortBadLt(builtin: u8) -> *mut lean_object {
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
  let res = initialize_qsortBadLt(1 /* builtin */);
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

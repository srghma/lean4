// Lean compiler output
// Module: array_test2
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_usize_dec_eq(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn l_Array_append___redArg(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_sub(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_array_fget_borrowed(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_nat_mod(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_usize_of_nat(_: *mut lean_object) -> usize;
}
#[no_mangle] pub static l_check___closed__0_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l_check___closed__0: *mut lean_object = core::ptr::addr_of!(l_check___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_array_object<3> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*3) as u16, m_other: 0, m_tag: 246 }, m_size: 3, m_capacity: 3, m_data: [((( 2 as usize) << 1) | 1) as *mut lean_object,((( 3 as usize) << 1) | 1) as *mut lean_object,((( 5 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: u8 = 0;
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: usize = 0;
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: u8 = 0;
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__7: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__8: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_main___closed__9_value: lean_array_object<6> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*6) as u16, m_other: 0, m_tag: 246 }, m_size: 6, m_capacity: 6, m_data: [((( 2 as usize) << 1) | 1) as *mut lean_object,((( 3 as usize) << 1) | 1) as *mut lean_object,((( 5 as usize) << 1) | 1) as *mut lean_object,((( 4 as usize) << 1) | 1) as *mut lean_object,((( 7 as usize) << 1) | 1) as *mut lean_object,((( 9 as usize) << 1) | 1) as *mut lean_object] };
static mut l_main___closed__9: *mut lean_object = core::ptr::addr_of!(l_main___closed__9_value) as *mut lean_object;
static mut l_main___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__10: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__11: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__12_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__12: u8 = 0;
static mut l_main___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__13: u8 = 0;
static mut l_main___closed__14_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__14: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__15_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__15: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__16_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__16: u8 = 0;
static mut l_main___closed__17_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__17: u8 = 0;
static mut l_main___closed__18_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__18: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__19_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__19: u8 = 0;
static mut l_main___closed__20_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__20: u8 = 0;
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00check_spec__0_spec__0(mut v_s_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_get_stdout();
v_putStr_4_ = lean_ctor_get(v___x_3_, 4);
lean_inc_ref(v_putStr_4_);
lean_dec_ref(v___x_3_);
v___x_5_ = lean_apply_2(v_putStr_4_, v_s_1_, lean_box(0));
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00check_spec__0_spec__0___boxed(mut v_s_6_: *mut lean_object, mut v_a_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_IO_print___at___00IO_println___at___00check_spec__0_spec__0(v_s_6_);
return v_res_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00check_spec__0(mut v_s_9_: *mut lean_object) -> *mut lean_object{
let mut v___x_11_: u32 = 0; let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = 10;
v___x_12_ = lean_string_push(v_s_9_, v___x_11_);
v___x_13_ = l_IO_print___at___00IO_println___at___00check_spec__0_spec__0(v___x_12_);
return v___x_13_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00check_spec__0___boxed(mut v_s_14_: *mut lean_object, mut v_a_15_: *mut lean_object) -> *mut lean_object{
let mut v_res_16_: *mut lean_object = core::ptr::null_mut(); 
v_res_16_ = l_IO_println___at___00check_spec__0(v_s_14_);
return v_res_16_;
}
#[no_mangle] pub unsafe extern "C" fn l_check(mut v_b_18_: u8) -> *mut lean_object{
if v_b_18_ == 0 {
let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); 
v___x_20_ = l_check___closed__0;
v___x_21_ = l_IO_println___at___00check_spec__0(v___x_20_);
return v___x_21_;
} else {
let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); 
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_check___boxed(mut v_b_24_: *mut lean_object, mut v_a_25_: *mut lean_object) -> *mut lean_object{
let mut v_b_boxed_26_: u8 = 0; let mut v_res_27_: *mut lean_object = core::ptr::null_mut(); 
v_b_boxed_26_ = (lean_unbox(v_b_24_) as u8);
v_res_27_ = l_check(v_b_boxed_26_);
return v_res_27_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__0(mut v_as_28_: *mut lean_object, mut v_i_29_: usize, mut v_stop_30_: usize) -> u8{
let mut v___x_31_: u8 = 0; let mut v___x_32_: u8 = 0; let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: u8 = 0; let mut v___x_36_: usize = 0; let mut v___x_37_: usize = 0; let mut v___x_39_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_31_ = lean_usize_dec_eq(v_i_29_, v_stop_30_);
if v___x_31_ == 0 {
let mut v___x_32_: u8 = 0; let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: u8 = 0; 
v___x_32_ = 1;
v___x_33_ = lean_array_uget_borrowed(v_as_28_, v_i_29_);
v___x_34_ = lean_unsigned_to_nat(10);
v___x_35_ = lean_nat_dec_lt(v___x_33_, v___x_34_);
if v___x_35_ == 0 {
return v___x_32_;
} else {
if v___x_31_ == 0 {
let mut v___x_36_: usize = 0; let mut v___x_37_: usize = 0; 
v___x_36_ = 1usize;
v___x_37_ = lean_usize_add(v_i_29_, v___x_36_);
v_i_29_ = v___x_37_;
state = 0; continue;
} else {
return v___x_32_;
}
}
} else {
let mut v___x_39_: u8 = 0; 
v___x_39_ = 0;
return v___x_39_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__0___boxed(mut v_as_40_: *mut lean_object, mut v_i_41_: *mut lean_object, mut v_stop_42_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_43_: usize = 0; let mut v_stop_boxed_44_: usize = 0; let mut v_res_45_: u8 = 0; let mut v_r_46_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_43_ = lean_unbox_usize(v_i_41_);
lean_dec(v_i_41_);
v_stop_boxed_44_ = lean_unbox_usize(v_stop_42_);
lean_dec(v_stop_42_);
v_res_45_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__0(v_as_40_, v_i_boxed_43_, v_stop_boxed_44_);
lean_dec_ref(v_as_40_);
v_r_46_ = lean_box((v_res_45_) as usize);
return v_r_46_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00main_spec__3___redArg(mut v_xs_47_: *mut lean_object, mut v_ys_48_: *mut lean_object, mut v_x_49_: *mut lean_object) -> u8{
let mut v_zero_50_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_51_: u8 = 0; let mut v_one_52_: *mut lean_object = core::ptr::null_mut(); let mut v_n_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_zero_50_ = lean_unsigned_to_nat(0);
v_isZero_51_ = lean_nat_dec_eq(v_x_49_, v_zero_50_);
if v_isZero_51_ == 1 {
lean_dec(v_x_49_);
return v_isZero_51_;
} else {
let mut v_one_52_: *mut lean_object = core::ptr::null_mut(); let mut v_n_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: u8 = 0; 
v_one_52_ = lean_unsigned_to_nat(1);
v_n_53_ = lean_nat_sub(v_x_49_, v_one_52_);
lean_dec(v_x_49_);
v___x_54_ = lean_array_fget_borrowed(v_xs_47_, v_n_53_);
v___x_55_ = lean_array_fget_borrowed(v_ys_48_, v_n_53_);
v___x_56_ = lean_nat_dec_eq(v___x_54_, v___x_55_);
if v___x_56_ == 0 {
lean_dec(v_n_53_);
return v___x_56_;
} else {
v_x_49_ = v_n_53_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00main_spec__3___redArg___boxed(mut v_xs_58_: *mut lean_object, mut v_ys_59_: *mut lean_object, mut v_x_60_: *mut lean_object) -> *mut lean_object{
let mut v_res_61_: u8 = 0; let mut v_r_62_: *mut lean_object = core::ptr::null_mut(); 
v_res_61_ = l_Array_isEqvAux___at___00main_spec__3___redArg(v_xs_58_, v_ys_59_, v_x_60_);
lean_dec_ref(v_ys_59_);
lean_dec_ref(v_xs_58_);
v_r_62_ = lean_box((v_res_61_) as usize);
return v_r_62_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__1(mut v_as_63_: *mut lean_object, mut v_i_64_: usize, mut v_stop_65_: usize) -> u8{
let mut v___x_66_: u8 = 0; let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: u8 = 0; let mut v___x_70_: usize = 0; let mut v___x_71_: usize = 0; let mut v___x_73_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_66_ = lean_usize_dec_eq(v_i_64_, v_stop_65_);
if v___x_66_ == 0 {
let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: u8 = 0; 
v___x_67_ = lean_array_uget_borrowed(v_as_63_, v_i_64_);
v___x_68_ = lean_unsigned_to_nat(10);
v___x_69_ = lean_nat_dec_lt(v___x_68_, v___x_67_);
if v___x_69_ == 0 {
let mut v___x_70_: usize = 0; let mut v___x_71_: usize = 0; 
v___x_70_ = 1usize;
v___x_71_ = lean_usize_add(v_i_64_, v___x_70_);
v_i_64_ = v___x_71_;
state = 0; continue;
} else {
return v___x_69_;
}
} else {
let mut v___x_73_: u8 = 0; 
v___x_73_ = 0;
return v___x_73_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__1___boxed(mut v_as_74_: *mut lean_object, mut v_i_75_: *mut lean_object, mut v_stop_76_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_77_: usize = 0; let mut v_stop_boxed_78_: usize = 0; let mut v_res_79_: u8 = 0; let mut v_r_80_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_77_ = lean_unbox_usize(v_i_75_);
lean_dec(v_i_75_);
v_stop_boxed_78_ = lean_unbox_usize(v_stop_76_);
lean_dec(v_stop_76_);
v_res_79_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__1(v_as_74_, v_i_boxed_77_, v_stop_boxed_78_);
lean_dec_ref(v_as_74_);
v_r_80_ = lean_box((v_res_79_) as usize);
return v_r_80_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__2(mut v_as_81_: *mut lean_object, mut v_i_82_: usize, mut v_stop_83_: usize) -> u8{
let mut v___x_84_: u8 = 0; let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: u8 = 0; let mut v___x_88_: usize = 0; let mut v___x_89_: usize = 0; let mut v___x_91_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_84_ = lean_usize_dec_eq(v_i_82_, v_stop_83_);
if v___x_84_ == 0 {
let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: u8 = 0; 
v___x_85_ = lean_unsigned_to_nat(4);
v___x_86_ = lean_array_uget_borrowed(v_as_81_, v_i_82_);
v___x_87_ = lean_nat_dec_lt(v___x_85_, v___x_86_);
if v___x_87_ == 0 {
let mut v___x_88_: usize = 0; let mut v___x_89_: usize = 0; 
v___x_88_ = 1usize;
v___x_89_ = lean_usize_add(v_i_82_, v___x_88_);
v_i_82_ = v___x_89_;
state = 0; continue;
} else {
return v___x_87_;
}
} else {
let mut v___x_91_: u8 = 0; 
v___x_91_ = 0;
return v___x_91_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__2___boxed(mut v_as_92_: *mut lean_object, mut v_i_93_: *mut lean_object, mut v_stop_94_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_95_: usize = 0; let mut v_stop_boxed_96_: usize = 0; let mut v_res_97_: u8 = 0; let mut v_r_98_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_95_ = lean_unbox_usize(v_i_93_);
lean_dec(v_i_93_);
v_stop_boxed_96_ = lean_unbox_usize(v_stop_94_);
lean_dec(v_stop_94_);
v_res_97_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__2(v_as_92_, v_i_boxed_95_, v_stop_boxed_96_);
lean_dec_ref(v_as_92_);
v_r_98_ = lean_box((v_res_97_) as usize);
return v_r_98_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00main_spec__4___redArg(mut v_xs_99_: *mut lean_object, mut v_ys_100_: *mut lean_object, mut v_x_101_: *mut lean_object) -> u8{
let mut v_zero_102_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_103_: u8 = 0; let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v_one_105_: *mut lean_object = core::ptr::null_mut(); let mut v_n_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_zero_102_ = lean_unsigned_to_nat(0);
v_isZero_103_ = lean_nat_dec_eq(v_x_101_, v_zero_102_);
if v_isZero_103_ == 1 {
lean_dec(v_x_101_);
return v_isZero_103_;
} else {
let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v_one_105_: *mut lean_object = core::ptr::null_mut(); let mut v_n_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v___x_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: u8 = 0; 
v___x_104_ = lean_unsigned_to_nat(2);
v_one_105_ = lean_unsigned_to_nat(1);
v_n_106_ = lean_nat_sub(v_x_101_, v_one_105_);
lean_dec(v_x_101_);
v___x_107_ = lean_array_fget_borrowed(v_xs_99_, v_n_106_);
v___x_108_ = lean_array_fget_borrowed(v_ys_100_, v_n_106_);
v___x_109_ = lean_nat_mod(v___x_107_, v___x_104_);
v___x_110_ = lean_nat_mod(v___x_108_, v___x_104_);
v___x_111_ = lean_nat_dec_eq(v___x_109_, v___x_110_);
lean_dec(v___x_110_);
lean_dec(v___x_109_);
if v___x_111_ == 0 {
lean_dec(v_n_106_);
return v___x_111_;
} else {
v_x_101_ = v_n_106_;
state = 0; continue;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00main_spec__4___redArg___boxed(mut v_xs_113_: *mut lean_object, mut v_ys_114_: *mut lean_object, mut v_x_115_: *mut lean_object) -> *mut lean_object{
let mut v_res_116_: u8 = 0; let mut v_r_117_: *mut lean_object = core::ptr::null_mut(); 
v_res_116_ = l_Array_isEqvAux___at___00main_spec__4___redArg(v_xs_113_, v_ys_114_, v_x_115_);
lean_dec_ref(v_ys_114_);
lean_dec_ref(v_xs_113_);
v_r_117_ = lean_box((v_res_116_) as usize);
return v_r_117_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v_a1_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); 
v_a1_125_ = l_main___closed__0;
v___x_126_ = lean_array_get_size(v_a1_125_);
return v___x_126_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> u8{
let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: u8 = 0; 
v___x_127_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_128_ = lean_unsigned_to_nat(0);
v___x_129_ = lean_nat_dec_lt(v___x_128_, v___x_127_);
return v___x_129_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> usize{
let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: usize = 0; 
v___x_130_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_131_ = lean_usize_of_nat(v___x_130_);
return v___x_131_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> u8{
let mut v___x_132_: usize = 0; let mut v___x_133_: usize = 0; let mut v_a1_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: u8 = 0; 
v___x_132_ = lean_usize_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_133_ = 0usize;
v_a1_134_ = l_main___closed__0;
v___x_135_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__2(v_a1_134_, v___x_133_, v___x_132_);
return v___x_135_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); 
v___x_136_ = lean_unsigned_to_nat(4);
v___x_137_ = lean_unsigned_to_nat(3);
v___x_138_ = lean_mk_empty_array_with_capacity(v___x_137_);
v___x_139_ = lean_array_push(v___x_138_, v___x_136_);
return v___x_139_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> *mut lean_object{
let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); 
v___x_140_ = lean_unsigned_to_nat(7);
v___x_141_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_142_ = lean_array_push(v___x_141_, v___x_140_);
return v___x_142_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__7() -> *mut lean_object{
let mut v___x_143_: *mut lean_object = core::ptr::null_mut(); let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v_a2_145_: *mut lean_object = core::ptr::null_mut(); 
v___x_143_ = lean_unsigned_to_nat(9);
v___x_144_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v_a2_145_ = lean_array_push(v___x_144_, v___x_143_);
return v_a2_145_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8() -> *mut lean_object{
let mut v_a2_146_: *mut lean_object = core::ptr::null_mut(); let mut v_a1_147_: *mut lean_object = core::ptr::null_mut(); let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); 
v_a2_146_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v_a1_147_ = l_main___closed__0;
v___x_148_ = l_Array_append___redArg(v_a1_147_, v_a2_146_);
return v___x_148_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10() -> *mut lean_object{
let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); 
v___x_163_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_164_ = lean_array_get_size(v___x_163_);
return v___x_164_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__11() -> *mut lean_object{
let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); 
v___x_165_ = l_main___closed__9;
v___x_166_ = lean_array_get_size(v___x_165_);
return v___x_166_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__12() -> u8{
let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); let mut v___x_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: u8 = 0; 
v___x_167_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v___x_168_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___x_169_ = lean_nat_dec_eq(v___x_168_, v___x_167_);
return v___x_169_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__13() -> u8{
let mut v___x_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); let mut v___x_172_: *mut lean_object = core::ptr::null_mut(); let mut v___x_173_: u8 = 0; 
v___x_170_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___x_171_ = l_main___closed__9;
v___x_172_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_173_ = l_Array_isEqvAux___at___00main_spec__3___redArg(v___x_172_, v___x_171_, v___x_170_);
return v___x_173_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__14() -> *mut lean_object{
let mut v___x_174_: *mut lean_object = core::ptr::null_mut(); let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v_a3_176_: *mut lean_object = core::ptr::null_mut(); 
v___x_174_ = lean_unsigned_to_nat(8);
v___x_175_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v_a3_176_ = lean_array_push(v___x_175_, v___x_174_);
return v_a3_176_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__15() -> *mut lean_object{
let mut v_a3_177_: *mut lean_object = core::ptr::null_mut(); let mut v___x_178_: *mut lean_object = core::ptr::null_mut(); 
v_a3_177_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__14), core::ptr::addr_of_mut!(l_main___closed__14_once), _init_l_main___closed__14);
v___x_178_ = lean_array_get_size(v_a3_177_);
return v___x_178_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__16() -> u8{
let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_180_: *mut lean_object = core::ptr::null_mut(); let mut v___x_181_: u8 = 0; 
v___x_179_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__15), core::ptr::addr_of_mut!(l_main___closed__15_once), _init_l_main___closed__15);
v___x_180_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_181_ = lean_nat_dec_eq(v___x_180_, v___x_179_);
return v___x_181_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__17() -> u8{
let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); let mut v_a3_183_: *mut lean_object = core::ptr::null_mut(); let mut v_a1_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: u8 = 0; 
v___x_182_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v_a3_183_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__14), core::ptr::addr_of_mut!(l_main___closed__14_once), _init_l_main___closed__14);
v_a1_184_ = l_main___closed__0;
v___x_185_ = l_Array_isEqvAux___at___00main_spec__4___redArg(v_a1_184_, v_a3_183_, v___x_182_);
return v___x_185_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__18() -> *mut lean_object{
let mut v_a2_186_: *mut lean_object = core::ptr::null_mut(); let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); 
v_a2_186_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_187_ = lean_array_get_size(v_a2_186_);
return v___x_187_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__19() -> u8{
let mut v___x_188_: *mut lean_object = core::ptr::null_mut(); let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); let mut v___x_190_: u8 = 0; 
v___x_188_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__18), core::ptr::addr_of_mut!(l_main___closed__18_once), _init_l_main___closed__18);
v___x_189_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_190_ = lean_nat_dec_eq(v___x_189_, v___x_188_);
return v___x_190_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__20() -> u8{
let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v_a2_192_: *mut lean_object = core::ptr::null_mut(); let mut v_a1_193_: *mut lean_object = core::ptr::null_mut(); let mut v___x_194_: u8 = 0; 
v___x_191_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v_a2_192_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v_a1_193_ = l_main___closed__0;
v___x_194_ = l_Array_isEqvAux___at___00main_spec__4___redArg(v_a1_193_, v_a2_192_, v___x_191_);
return v___x_194_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v_a1_196_: *mut lean_object = core::ptr::null_mut(); let mut v___y_198_: *mut lean_object = core::ptr::null_mut(); let mut v___y_199_: *mut lean_object = core::ptr::null_mut(); let mut v___y_200_: u8 = 0; let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); let mut v___x_202_: u8 = 0; let mut v___x_203_: u8 = 0; let mut v___x_204_: *mut lean_object = core::ptr::null_mut(); let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); let mut v___x_206_: usize = 0; let mut v___x_207_: usize = 0; let mut v___x_208_: u8 = 0; let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: u8 = 0; let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); let mut v___y_213_: *mut lean_object = core::ptr::null_mut(); let mut v___y_214_: *mut lean_object = core::ptr::null_mut(); let mut v___x_215_: u8 = 0; let mut v___y_217_: *mut lean_object = core::ptr::null_mut(); let mut v___y_218_: *mut lean_object = core::ptr::null_mut(); let mut v___y_219_: u8 = 0; let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v___x_221_: u8 = 0; let mut v___x_222_: usize = 0; let mut v___x_223_: usize = 0; let mut v___x_224_: u8 = 0; let mut v___x_225_: u8 = 0; let mut v___y_227_: u8 = 0; let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: u8 = 0; let mut v___x_232_: u8 = 0; let mut v___y_234_: u8 = 0; let mut v___x_235_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: u8 = 0; let mut v___x_237_: u8 = 0; let mut v___x_239_: u8 = 0; let mut v___y_241_: u8 = 0; let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); let mut v___x_243_: u8 = 0; let mut v___x_244_: u8 = 0; let mut v___x_245_: u8 = 0; let mut v___x_246_: u8 = 0; let mut v___x_247_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v_a1_196_ = l_main___closed__0;
v___x_246_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__19), core::ptr::addr_of_mut!(l_main___closed__19_once), _init_l_main___closed__19);
if v___x_246_ == 0 {
v___y_241_ = v___x_246_;
state = 7; continue;
} else {
let mut v___x_247_: u8 = 0; 
v___x_247_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__20), core::ptr::addr_of_mut!(l_main___closed__20_once), _init_l_main___closed__20);
v___y_241_ = v___x_247_;
state = 7; continue;
}
}
1 => {
v___x_201_ = l_check(v___y_200_);
if lean_obj_tag(v___x_201_) == 0 {
let mut v___x_202_: u8 = 0; 
lean_dec_ref_known(v___x_201_, 1);
v___x_202_ = lean_nat_dec_lt(v___y_199_, v___y_198_);
if v___x_202_ == 0 {
let mut v___x_203_: u8 = 0; let mut v___x_204_: *mut lean_object = core::ptr::null_mut(); 
v___x_203_ = 1;
v___x_204_ = l_check(v___x_203_);
return v___x_204_;
} else {
if v___x_202_ == 0 {
let mut v___x_205_: *mut lean_object = core::ptr::null_mut(); 
v___x_205_ = l_check(v___x_202_);
return v___x_205_;
} else {
let mut v___x_206_: usize = 0; let mut v___x_207_: usize = 0; let mut v___x_208_: u8 = 0; 
v___x_206_ = 0usize;
v___x_207_ = lean_usize_of_nat(v___y_198_);
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__0(v_a1_196_, v___x_206_, v___x_207_);
if v___x_208_ == 0 {
let mut v___x_209_: *mut lean_object = core::ptr::null_mut(); 
v___x_209_ = l_check(v___x_202_);
return v___x_209_;
} else {
let mut v___x_210_: u8 = 0; let mut v___x_211_: *mut lean_object = core::ptr::null_mut(); 
v___x_210_ = 0;
v___x_211_ = l_check(v___x_210_);
return v___x_211_;
}
}
}
} else {
return v___x_201_;
}
}
2 => {
v___x_215_ = 1;
v___y_198_ = v___y_213_;
v___y_199_ = v___y_214_;
v___y_200_ = v___x_215_;
state = 1; continue;
}
3 => {
v___x_220_ = l_check(v___y_219_);
if lean_obj_tag(v___x_220_) == 0 {
let mut v___x_221_: u8 = 0; 
lean_dec_ref_known(v___x_220_, 1);
v___x_221_ = lean_nat_dec_lt(v___y_218_, v___y_217_);
if v___x_221_ == 0 {
v___y_213_ = v___y_217_;
v___y_214_ = v___y_218_;
state = 2; continue;
} else {
if v___x_221_ == 0 {
v___y_213_ = v___y_217_;
v___y_214_ = v___y_218_;
state = 2; continue;
} else {
let mut v___x_222_: usize = 0; let mut v___x_223_: usize = 0; let mut v___x_224_: u8 = 0; 
v___x_222_ = 0usize;
v___x_223_ = lean_usize_of_nat(v___y_217_);
v___x_224_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00main_spec__1(v_a1_196_, v___x_222_, v___x_223_);
if v___x_224_ == 0 {
v___y_213_ = v___y_217_;
v___y_214_ = v___y_218_;
state = 2; continue;
} else {
let mut v___x_225_: u8 = 0; 
v___x_225_ = 0;
v___y_198_ = v___y_217_;
v___y_199_ = v___y_218_;
v___y_200_ = v___x_225_;
state = 1; continue;
}
}
}
} else {
return v___x_220_;
}
}
4 => {
v___x_228_ = l_check(v___y_227_);
if lean_obj_tag(v___x_228_) == 0 {
let mut v___x_229_: *mut lean_object = core::ptr::null_mut(); let mut v___x_230_: *mut lean_object = core::ptr::null_mut(); let mut v___x_231_: u8 = 0; 
lean_dec_ref_known(v___x_228_, 1);
v___x_229_ = lean_unsigned_to_nat(0);
v___x_230_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_231_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
if v___x_231_ == 0 {
v___y_217_ = v___x_230_;
v___y_218_ = v___x_229_;
v___y_219_ = v___x_231_;
state = 3; continue;
} else {
if v___x_231_ == 0 {
v___y_217_ = v___x_230_;
v___y_218_ = v___x_229_;
v___y_219_ = v___x_231_;
state = 3; continue;
} else {
let mut v___x_232_: u8 = 0; 
v___x_232_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___y_217_ = v___x_230_;
v___y_218_ = v___x_229_;
v___y_219_ = v___x_232_;
state = 3; continue;
}
}
} else {
return v___x_228_;
}
}
5 => {
v___x_235_ = l_check(v___y_234_);
if lean_obj_tag(v___x_235_) == 0 {
let mut v___x_236_: u8 = 0; 
lean_dec_ref_known(v___x_235_, 1);
v___x_236_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
if v___x_236_ == 0 {
v___y_227_ = v___x_236_;
state = 4; continue;
} else {
let mut v___x_237_: u8 = 0; 
v___x_237_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__13), core::ptr::addr_of_mut!(l_main___closed__13_once), _init_l_main___closed__13);
v___y_227_ = v___x_237_;
state = 4; continue;
}
} else {
return v___x_235_;
}
}
6 => {
v___x_239_ = 1;
v___y_234_ = v___x_239_;
state = 5; continue;
}
7 => {
v___x_242_ = l_check(v___y_241_);
if lean_obj_tag(v___x_242_) == 0 {
let mut v___x_243_: u8 = 0; 
lean_dec_ref_known(v___x_242_, 1);
v___x_243_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__16), core::ptr::addr_of_mut!(l_main___closed__16_once), _init_l_main___closed__16);
if v___x_243_ == 0 {
state = 6; continue;
} else {
let mut v___x_244_: u8 = 0; 
v___x_244_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
if v___x_244_ == 0 {
state = 6; continue;
} else {
let mut v___x_245_: u8 = 0; 
v___x_245_ = 0;
v___y_234_ = v___x_245_;
state = 5; continue;
}
}
} else {
return v___x_242_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_248_: *mut lean_object) -> *mut lean_object{
let mut v_res_249_: *mut lean_object = core::ptr::null_mut(); 
v_res_249_ = _lean_main();
return v_res_249_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00main_spec__3(mut v_xs_250_: *mut lean_object, mut v_ys_251_: *mut lean_object, mut v_hsz_252_: *mut lean_object, mut v_x_253_: *mut lean_object, mut v_x_254_: *mut lean_object) -> u8{
let mut v___x_255_: u8 = 0; 
v___x_255_ = l_Array_isEqvAux___at___00main_spec__3___redArg(v_xs_250_, v_ys_251_, v_x_253_);
return v___x_255_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00main_spec__3___boxed(mut v_xs_256_: *mut lean_object, mut v_ys_257_: *mut lean_object, mut v_hsz_258_: *mut lean_object, mut v_x_259_: *mut lean_object, mut v_x_260_: *mut lean_object) -> *mut lean_object{
let mut v_res_261_: u8 = 0; let mut v_r_262_: *mut lean_object = core::ptr::null_mut(); 
v_res_261_ = l_Array_isEqvAux___at___00main_spec__3(v_xs_256_, v_ys_257_, v_hsz_258_, v_x_259_, v_x_260_);
lean_dec_ref(v_ys_257_);
lean_dec_ref(v_xs_256_);
v_r_262_ = lean_box((v_res_261_) as usize);
return v_r_262_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00main_spec__4(mut v_xs_263_: *mut lean_object, mut v_ys_264_: *mut lean_object, mut v_hsz_265_: *mut lean_object, mut v_x_266_: *mut lean_object, mut v_x_267_: *mut lean_object) -> u8{
let mut v___x_268_: u8 = 0; 
v___x_268_ = l_Array_isEqvAux___at___00main_spec__4___redArg(v_xs_263_, v_ys_264_, v_x_266_);
return v___x_268_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_isEqvAux___at___00main_spec__4___boxed(mut v_xs_269_: *mut lean_object, mut v_ys_270_: *mut lean_object, mut v_hsz_271_: *mut lean_object, mut v_x_272_: *mut lean_object, mut v_x_273_: *mut lean_object) -> *mut lean_object{
let mut v_res_274_: u8 = 0; let mut v_r_275_: *mut lean_object = core::ptr::null_mut(); 
v_res_274_ = l_Array_isEqvAux___at___00main_spec__4(v_xs_269_, v_ys_270_, v_hsz_271_, v_x_272_, v_x_273_);
lean_dec_ref(v_ys_270_);
lean_dec_ref(v_xs_269_);
v_r_275_ = lean_box((v_res_274_) as usize);
return v_r_275_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_array__test2(builtin: u8) -> *mut lean_object {
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
  let res = initialize_array__test2(1 /* builtin */);
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

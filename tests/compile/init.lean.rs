// Lean compiler output
// Module: init
// Imports: public import Init public meta import Init
use lean_runtime::generated_abi::*;
extern "C" {
    fn lean_mk_empty_array_with_capacity(_: *mut lean_object) -> *mut lean_object;
    fn lean_st_mk_ref(_: *mut lean_object) -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_st_ref_get(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_get_size(_: *mut lean_object) -> *mut lean_object;
    fn lean_nat_dec_lt(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_usize_of_nat(_: *mut lean_object) -> usize;
    fn lean_usize_dec_eq(_: usize, _: usize) -> u8;
    fn lean_array_uget_borrowed(_: *mut lean_object, _: usize) -> *mut lean_object;
    fn lean_string_dec_eq(_: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_usize_add(_: usize, _: usize) -> usize;
    fn lean_st_ref_take(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_push(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_st_ref_set(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_nat_add(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn l_Nat_reprFast(_: *mut lean_object) -> *mut lean_object;
    fn lean_array_to_list(_: *mut lean_object) -> *mut lean_object;
}
#[no_mangle] pub static mut l_Foo_ref: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l___private_init_0__Foo_initFn___closed__0_00___x40_init_3039496628____hygCtx___hyg_2__value: lean_array_object<0> = lean_array_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut lean_object>()*0) as u16, m_other: 0, m_tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_init_0__Foo_initFn___closed__0_00___x40_init_3039496628____hygCtx___hyg_2_: *mut lean_object = core::ptr::addr_of!(l___private_init_0__Foo_initFn___closed__0_00___x40_init_3039496628____hygCtx___hyg_2__value) as *mut lean_object;
#[no_mangle] pub static mut l_Foo_vals: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub static l_Foo_registerVal___closed__0_value: lean_string_object<25> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [118, 97, 108, 117, 101, 32, 97, 108, 114, 101, 97, 100, 121, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 0]};
static mut l_Foo_registerVal___closed__0: *mut lean_object = core::ptr::addr_of!(l_Foo_registerVal___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_Foo_registerVal___closed__1_value: lean_ctor_object<1> = lean_ctor_object { m_header: lean_object { m_rc: 0, m_cs_sz: (core::mem::size_of::<lean_object>() + core::mem::size_of::<*mut lean_object>()*1 + 0) as u16, m_other: 1, m_tag: 18 }, m_objs: [core::ptr::addr_of!(l_Foo_registerVal___closed__0_value) as *mut lean_object] };
static mut l_Foo_registerVal___closed__1: *mut lean_object = core::ptr::addr_of!(l_Foo_registerVal___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l___private_init_0__Foo_initFn___closed__0_00___x40_init_552206657____hygCtx___hyg_2__value: lean_string_object<20> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [115, 116, 97, 114, 116, 101, 100, 32, 116, 104, 101, 32, 112, 114, 111, 103, 114, 97, 109, 0]};
static mut l___private_init_0__Foo_initFn___closed__0_00___x40_init_552206657____hygCtx___hyg_2_: *mut lean_object = core::ptr::addr_of!(l___private_init_0__Foo_initFn___closed__0_00___x40_init_552206657____hygCtx___hyg_2__value) as *mut lean_object;
#[no_mangle] pub static l___private_init_0__Foo_initFn___closed__1_00___x40_init_552206657____hygCtx___hyg_2__value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 101, 108, 108, 111, 0]};
static mut l___private_init_0__Foo_initFn___closed__1_00___x40_init_552206657____hygCtx___hyg_2_: *mut lean_object = core::ptr::addr_of!(l___private_init_0__Foo_initFn___closed__1_00___x40_init_552206657____hygCtx___hyg_2__value) as *mut lean_object;
#[no_mangle] pub static l___private_init_0__Foo_initFn___closed__0_00___x40_init_3259079772____hygCtx___hyg_2__value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [119, 111, 114, 108, 100, 0]};
static mut l___private_init_0__Foo_initFn___closed__0_00___x40_init_3259079772____hygCtx___hyg_2_: *mut lean_object = core::ptr::addr_of!(l___private_init_0__Foo_initFn___closed__0_00___x40_init_3259079772____hygCtx___hyg_2__value) as *mut lean_object;
#[no_mangle] pub static l___private_init_0__Foo_initFn___closed__0_00___x40_init_2380757050____hygCtx___hyg_2__value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 111, 111, 0]};
static mut l___private_init_0__Foo_initFn___closed__0_00___x40_init_2380757050____hygCtx___hyg_2_: *mut lean_object = core::ptr::addr_of!(l___private_init_0__Foo_initFn___closed__0_00___x40_init_2380757050____hygCtx___hyg_2__value) as *mut lean_object;
#[no_mangle] pub static l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__1_spec__2___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__1_spec__2___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__1_spec__2___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__1_value) as *mut lean_object;
#[no_mangle] pub static l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__2_value) as *mut lean_object;
#[no_mangle] pub static l_IO_println___at___00main_spec__1___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [35, 0]};
static mut l_IO_println___at___00main_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__1___closed__0_value) as *mut lean_object;
#[no_mangle] pub static l_main___closed__0_value: lean_string_object<12> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_3231478276____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_2_: *mut lean_object = core::ptr::null_mut(); let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v___x_4_: *mut lean_object = core::ptr::null_mut(); 
v___x_2_ = lean_unsigned_to_nat(10);
v___x_3_ = lean_st_mk_ref(v___x_2_);
v___x_4_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_3231478276____hygCtx___hyg_2____boxed(mut v_a_5_: *mut lean_object) -> *mut lean_object{
let mut v_res_6_: *mut lean_object = core::ptr::null_mut(); 
v_res_6_ = l___private_init_0__Foo_initFn_00___x40_init_3231478276____hygCtx___hyg_2_();
return v_res_6_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_3039496628____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); 
v___x_10_ = l___private_init_0__Foo_initFn___closed__0_00___x40_init_3039496628____hygCtx___hyg_2_;
v___x_11_ = lean_st_mk_ref(v___x_10_);
v___x_12_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_3039496628____hygCtx___hyg_2____boxed(mut v_a_13_: *mut lean_object) -> *mut lean_object{
let mut v_res_14_: *mut lean_object = core::ptr::null_mut(); 
v_res_14_ = l___private_init_0__Foo_initFn_00___x40_init_3039496628____hygCtx___hyg_2_();
return v_res_14_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Foo_registerVal_spec__0_spec__0(mut v_a_15_: *mut lean_object, mut v_as_16_: *mut lean_object, mut v_i_17_: usize, mut v_stop_18_: usize) -> u8{
let mut v___x_19_: u8 = 0; let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: u8 = 0; let mut v___x_22_: usize = 0; let mut v___x_23_: usize = 0; let mut v___x_25_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_19_ = lean_usize_dec_eq(v_i_17_, v_stop_18_);
if v___x_19_ == 0 {
let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: u8 = 0; 
v___x_20_ = lean_array_uget_borrowed(v_as_16_, v_i_17_);
v___x_21_ = lean_string_dec_eq(v_a_15_, v___x_20_);
if v___x_21_ == 0 {
let mut v___x_22_: usize = 0; let mut v___x_23_: usize = 0; 
v___x_22_ = 1usize;
v___x_23_ = lean_usize_add(v_i_17_, v___x_22_);
v_i_17_ = v___x_23_;
state = 0; continue;
} else {
return v___x_21_;
}
} else {
let mut v___x_25_: u8 = 0; 
v___x_25_ = 0;
return v___x_25_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Foo_registerVal_spec__0_spec__0___boxed(mut v_a_26_: *mut lean_object, mut v_as_27_: *mut lean_object, mut v_i_28_: *mut lean_object, mut v_stop_29_: *mut lean_object) -> *mut lean_object{
let mut v_i_boxed_30_: usize = 0; let mut v_stop_boxed_31_: usize = 0; let mut v_res_32_: u8 = 0; let mut v_r_33_: *mut lean_object = core::ptr::null_mut(); 
v_i_boxed_30_ = lean_unbox_usize(v_i_28_);
lean_dec(v_i_28_);
v_stop_boxed_31_ = lean_unbox_usize(v_stop_29_);
lean_dec(v_stop_29_);
v_res_32_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Foo_registerVal_spec__0_spec__0(v_a_26_, v_as_27_, v_i_boxed_30_, v_stop_boxed_31_);
lean_dec_ref(v_as_27_);
lean_dec_ref(v_a_26_);
v_r_33_ = lean_box((v_res_32_) as usize);
return v_r_33_;
}
#[no_mangle] pub unsafe extern "C" fn l_Array_contains___at___00Foo_registerVal_spec__0(mut v_as_34_: *mut lean_object, mut v_a_35_: *mut lean_object) -> u8{
let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_38_: u8 = 0; 
v___x_36_ = lean_unsigned_to_nat(0);
v___x_37_ = lean_array_get_size(v_as_34_);
v___x_38_ = lean_nat_dec_lt(v___x_36_, v___x_37_);
if v___x_38_ == 0 {
return v___x_38_;
} else {
if v___x_38_ == 0 {
return v___x_38_;
} else {
let mut v___x_39_: usize = 0; let mut v___x_40_: usize = 0; let mut v___x_41_: u8 = 0; 
v___x_39_ = 0usize;
v___x_40_ = lean_usize_of_nat(v___x_37_);
v___x_41_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Foo_registerVal_spec__0_spec__0(v_a_35_, v_as_34_, v___x_39_, v___x_40_);
return v___x_41_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_Array_contains___at___00Foo_registerVal_spec__0___boxed(mut v_as_42_: *mut lean_object, mut v_a_43_: *mut lean_object) -> *mut lean_object{
let mut v_res_44_: u8 = 0; let mut v_r_45_: *mut lean_object = core::ptr::null_mut(); 
v_res_44_ = l_Array_contains___at___00Foo_registerVal_spec__0(v_as_42_, v_a_43_);
lean_dec_ref(v_a_43_);
lean_dec_ref(v_as_42_);
v_r_45_ = lean_box((v_res_44_) as usize);
return v_r_45_;
}
#[no_mangle] pub unsafe extern "C" fn l_Foo_registerVal(mut v_s_49_: *mut lean_object) -> *mut lean_object{
let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: u8 = 0; 
v___x_51_ = l_Foo_vals;
v___x_52_ = lean_st_ref_get(v___x_51_);
v___x_53_ = l_Array_contains___at___00Foo_registerVal_spec__0(v___x_52_, v_s_49_);
lean_dec(v___x_52_);
if v___x_53_ == 0 {
let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); 
v___x_54_ = lean_st_ref_take(v___x_51_);
v___x_55_ = lean_array_push(v___x_54_, v_s_49_);
v___x_56_ = lean_st_ref_set(v___x_51_, v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
} else {
let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref(v_s_49_);
v___x_58_ = l_Foo_registerVal___closed__1;
v___x_59_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_Foo_registerVal___boxed(mut v_s_60_: *mut lean_object, mut v_a_61_: *mut lean_object) -> *mut lean_object{
let mut v_res_62_: *mut lean_object = core::ptr::null_mut(); 
v_res_62_ = l_Foo_registerVal(v_s_60_);
return v_res_62_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0_spec__0(mut v_s_63_: *mut lean_object) -> *mut lean_object{
let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
v___x_65_ = lean_get_stdout();
v_putStr_66_ = lean_ctor_get(v___x_65_, 4);
lean_inc_ref(v_putStr_66_);
lean_dec_ref(v___x_65_);
v___x_67_ = lean_apply_2(v_putStr_66_, v_s_63_, lean_box(0));
return v___x_67_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0_spec__0___boxed(mut v_s_68_: *mut lean_object, mut v_a_69_: *mut lean_object) -> *mut lean_object{
let mut v_res_70_: *mut lean_object = core::ptr::null_mut(); 
v_res_70_ = l_IO_print___at___00IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0_spec__0(v_s_68_);
return v_res_70_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0(mut v_s_71_: *mut lean_object) -> *mut lean_object{
let mut v___x_73_: u32 = 0; let mut v___x_74_: *mut lean_object = core::ptr::null_mut(); let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); 
v___x_73_ = 10;
v___x_74_ = lean_string_push(v_s_71_, v___x_73_);
v___x_75_ = l_IO_print___at___00IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0_spec__0(v___x_74_);
return v___x_75_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0___boxed(mut v_s_76_: *mut lean_object, mut v_a_77_: *mut lean_object) -> *mut lean_object{
let mut v_res_78_: *mut lean_object = core::ptr::null_mut(); 
v_res_78_ = l_IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0(v_s_76_);
return v_res_78_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); 
v___x_82_ = l___private_init_0__Foo_initFn___closed__0_00___x40_init_552206657____hygCtx___hyg_2_;
v___x_83_ = l_IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0(v___x_82_);
if lean_obj_tag(v___x_83_) == 0 {
let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_83_, 1);
v___x_84_ = l_Foo_ref;
v___x_85_ = lean_st_ref_take(v___x_84_);
v___x_86_ = lean_unsigned_to_nat(20);
v___x_87_ = lean_nat_add(v___x_85_, v___x_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_st_ref_set(v___x_84_, v___x_87_);
v___x_89_ = l___private_init_0__Foo_initFn___closed__1_00___x40_init_552206657____hygCtx___hyg_2_;
v___x_90_ = l_Foo_registerVal(v___x_89_);
return v___x_90_;
} else {
return v___x_83_;
}
}
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2____boxed(mut v_a_91_: *mut lean_object) -> *mut lean_object{
let mut v_res_92_: *mut lean_object = core::ptr::null_mut(); 
v_res_92_ = l___private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2_();
return v_res_92_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_3259079772____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); 
v___x_95_ = l___private_init_0__Foo_initFn___closed__0_00___x40_init_3259079772____hygCtx___hyg_2_;
v___x_96_ = l_Foo_registerVal(v___x_95_);
return v___x_96_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_3259079772____hygCtx___hyg_2____boxed(mut v_a_97_: *mut lean_object) -> *mut lean_object{
let mut v_res_98_: *mut lean_object = core::ptr::null_mut(); 
v_res_98_ = l___private_init_0__Foo_initFn_00___x40_init_3259079772____hygCtx___hyg_2_();
return v_res_98_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_2380757050____hygCtx___hyg_2_() -> *mut lean_object{
let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: *mut lean_object = core::ptr::null_mut(); 
v___x_101_ = l___private_init_0__Foo_initFn___closed__0_00___x40_init_2380757050____hygCtx___hyg_2_;
v___x_102_ = l_Foo_registerVal(v___x_101_);
return v___x_102_;
}
#[no_mangle] pub unsafe extern "C" fn l___private_init_0__Foo_initFn_00___x40_init_2380757050____hygCtx___hyg_2____boxed(mut v_a_103_: *mut lean_object) -> *mut lean_object{
let mut v_res_104_: *mut lean_object = core::ptr::null_mut(); 
v_res_104_ = l___private_init_0__Foo_initFn_00___x40_init_2380757050____hygCtx___hyg_2_();
return v_res_104_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__1_spec__2(mut v_x_106_: *mut lean_object, mut v_x_107_: *mut lean_object) -> *mut lean_object{
let mut v_head_108_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_107_) == 0 {
return v_x_106_;
} else {
let mut v_head_108_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); 
v_head_108_ = lean_ctor_get(v_x_107_, 0);
v_tail_109_ = lean_ctor_get(v_x_107_, 1);
v___x_110_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__1_spec__2___closed__0;
v___x_111_ = lean_string_append(v_x_106_, v___x_110_);
v___x_112_ = lean_string_append(v___x_111_, v_head_108_);
v_x_106_ = v___x_112_;
v_x_107_ = v_tail_109_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__1_spec__2___boxed(mut v_x_114_: *mut lean_object, mut v_x_115_: *mut lean_object) -> *mut lean_object{
let mut v_res_116_: *mut lean_object = core::ptr::null_mut(); 
v_res_116_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__1_spec__2(v_x_114_, v_x_115_);
lean_dec(v_x_115_);
return v_res_116_;
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00main_spec__1_spec__1(mut v_x_120_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_120_) == 0 {
let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); 
v___x_121_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__0;
return v___x_121_;
} else {
let mut v_tail_122_: *mut lean_object = core::ptr::null_mut(); 
v_tail_122_ = lean_ctor_get(v_x_120_, 1);
if lean_obj_tag(v_tail_122_) == 0 {
let mut v_head_123_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v___x_127_: *mut lean_object = core::ptr::null_mut(); 
v_head_123_ = lean_ctor_get(v_x_120_, 0);
v___x_124_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__1;
v___x_125_ = lean_string_append(v___x_124_, v_head_123_);
v___x_126_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__2;
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
return v___x_127_;
} else {
let mut v_head_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: u32 = 0; let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); 
v_head_128_ = lean_ctor_get(v_x_120_, 0);
v___x_129_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___closed__1;
v___x_130_ = lean_string_append(v___x_129_, v_head_128_);
v___x_131_ = l_List_foldl___at___00List_toString___at___00IO_println___at___00main_spec__1_spec__1_spec__2(v___x_130_, v_tail_122_);
v___x_132_ = 93;
v___x_133_ = lean_string_push(v___x_131_, v___x_132_);
return v___x_133_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00IO_println___at___00main_spec__1_spec__1___boxed(mut v_x_134_: *mut lean_object) -> *mut lean_object{
let mut v_res_135_: *mut lean_object = core::ptr::null_mut(); 
v_res_135_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__1(v_x_134_);
lean_dec(v_x_134_);
return v_res_135_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_137_: *mut lean_object) -> *mut lean_object{
let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: u32 = 0; let mut v___x_144_: *mut lean_object = core::ptr::null_mut(); let mut v___x_145_: *mut lean_object = core::ptr::null_mut(); 
v___x_139_ = l_IO_println___at___00main_spec__1___closed__0;
v___x_140_ = lean_array_to_list(v_s_137_);
v___x_141_ = l_List_toString___at___00IO_println___at___00main_spec__1_spec__1(v___x_140_);
lean_dec(v___x_140_);
v___x_142_ = lean_string_append(v___x_139_, v___x_141_);
lean_dec_ref(v___x_141_);
v___x_143_ = 10;
v___x_144_ = lean_string_push(v___x_142_, v___x_143_);
v___x_145_ = l_IO_print___at___00IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0_spec__0(v___x_144_);
return v___x_145_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_146_: *mut lean_object, mut v_a_147_: *mut lean_object) -> *mut lean_object{
let mut v_res_148_: *mut lean_object = core::ptr::null_mut(); 
v_res_148_ = l_IO_println___at___00main_spec__1(v_s_146_);
return v_res_148_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_149_: *mut lean_object) -> *mut lean_object{
let mut v___x_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: u32 = 0; let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); 
v___x_151_ = l_Nat_reprFast(v_s_149_);
v___x_152_ = 10;
v___x_153_ = lean_string_push(v___x_151_, v___x_152_);
v___x_154_ = l_IO_print___at___00IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0_spec__0(v___x_153_);
return v___x_154_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_155_: *mut lean_object, mut v_a_156_: *mut lean_object) -> *mut lean_object{
let mut v_res_157_: *mut lean_object = core::ptr::null_mut(); 
v_res_157_ = l_IO_println___at___00main_spec__0(v_s_155_);
return v_res_157_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); 
v___x_160_ = l_main___closed__0;
v___x_161_ = l_IO_println___at___00__private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2__spec__0(v___x_160_);
if lean_obj_tag(v___x_161_) == 0 {
let mut v___x_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); let mut v___x_164_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_161_, 1);
v___x_162_ = l_Foo_ref;
v___x_163_ = lean_st_ref_get(v___x_162_);
v___x_164_ = l_IO_println___at___00main_spec__0(v___x_163_);
if lean_obj_tag(v___x_164_) == 0 {
let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v___x_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_164_, 1);
v___x_165_ = l_Foo_vals;
v___x_166_ = lean_st_ref_get(v___x_165_);
v___x_167_ = l_IO_println___at___00main_spec__1(v___x_166_);
return v___x_167_;
} else {
return v___x_164_;
}
} else {
return v___x_161_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_168_: *mut lean_object) -> *mut lean_object{
let mut v_res_169_: *mut lean_object = core::ptr::null_mut(); 
v_res_169_ = _lean_main();
return v_res_169_;
}
extern "C" { fn initialize_Init(builtin: u8) -> *mut lean_object; }
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_init(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = l___private_init_0__Foo_initFn_00___x40_init_3231478276____hygCtx___hyg_2_();
if lean_io_result_is_error(res) { return res; }
l_Foo_ref = lean_io_result_get_value(res);
lean_mark_persistent(l_Foo_ref);
lean_dec_ref(res);
res = l___private_init_0__Foo_initFn_00___x40_init_3039496628____hygCtx___hyg_2_();
if lean_io_result_is_error(res) { return res; }
l_Foo_vals = lean_io_result_get_value(res);
lean_mark_persistent(l_Foo_vals);
lean_dec_ref(res);
res = l___private_init_0__Foo_initFn_00___x40_init_552206657____hygCtx___hyg_2_();
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = l___private_init_0__Foo_initFn_00___x40_init_3259079772____hygCtx___hyg_2_();
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = l___private_init_0__Foo_initFn_00___x40_init_2380757050____hygCtx___hyg_2_();
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
  let res = initialize_init(1 /* builtin */);
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

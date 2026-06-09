// Lean compiler output
// Module: str
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Pattern::Basic::*;
use lean_init::Init::Data::String::Slice::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::String::Basic::*;
use lean_init::Init::Data::Format::Basic::*;
use lean_init::Init::Data::String::Defs::*;
extern "C" {
    fn lean_string_memcmp(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> u8;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_string_utf8_extract(_: *mut lean_object, _: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_get(_: *mut lean_object, _: *mut lean_object) -> u32;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_utf8_next(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
}
pub static l_showChars___closed__0_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [62, 62, 32, 0]};
static mut l_showChars___closed__0: *mut lean_object = core::ptr::addr_of!(l_showChars___closed__0_value) as *mut lean_object;
pub static l_showChars___closed__1_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_showChars___closed__1: *mut lean_object = core::ptr::addr_of!(l_showChars___closed__1_value) as *mut lean_object;
pub static l_IO_println___at___00main_spec__1___closed__0_value: lean_string_object<6> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_IO_println___at___00main_spec__1___closed__0: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__1___closed__0_value) as *mut lean_object;
pub static l_IO_println___at___00main_spec__1___closed__1_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_IO_println___at___00main_spec__1___closed__1: *mut lean_object = core::ptr::addr_of!(l_IO_println___at___00main_spec__1___closed__1_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 2, m_data: [206, 177, 98, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
pub static l_main___closed__1_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 3, m_data: [206, 177, 98, 99, 0]};
static mut l_main___closed__1: *mut lean_object = core::ptr::addr_of!(l_main___closed__1_value) as *mut lean_object;
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: u8 = 0;
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: u8 = 0;
pub static l_main___closed__6_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 98, 0]};
static mut l_main___closed__6: *mut lean_object = core::ptr::addr_of!(l_main___closed__6_value) as *mut lean_object;
pub static l_main___closed__7_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l_main___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object;
static mut l_main___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__8: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__9: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__10: u8 = 0;
static mut l_main___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__11: u8 = 0;
pub static l_main___closed__12_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [99, 98, 0]};
static mut l_main___closed__12: *mut lean_object = core::ptr::addr_of!(l_main___closed__12_value) as *mut lean_object;
static mut l_main___closed__13_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__13: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__14_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__14: u8 = 0;
static mut l_main___closed__15_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__15: u8 = 0;
static mut l_main___closed__16_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__16: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__17_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__17: u8 = 0;
static mut l_main___closed__18_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__18: u8 = 0;
pub static l_main___closed__19_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 98, 99, 100, 0]};
static mut l_main___closed__19: *mut lean_object = core::ptr::addr_of!(l_main___closed__19_value) as *mut lean_object;
static mut l_main___closed__20_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__20: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__21_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__21: u8 = 0;
static mut l_main___closed__22_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__22: u8 = 0;
static mut l_main___closed__23_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__23: u8 = 0;
static mut l_main___closed__24_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__24: u8 = 0;
pub static l_main___closed__25_value: lean_string_object<18> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 18, m_capacity: 18, m_length: 15, m_data: [104, 101, 108, 108, 111, 32, 206, 177, 95, 119, 111, 114, 108, 100, 95, 206, 178, 0]};
static mut l_main___closed__25: *mut lean_object = core::ptr::addr_of!(l_main___closed__25_value) as *mut lean_object;
static mut l_main___closed__26_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__26: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__27_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 32, 0]};
static mut l_main___closed__27: *mut lean_object = core::ptr::addr_of!(l_main___closed__27_value) as *mut lean_object;
static mut l_main___closed__28_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__28: *mut lean_object = core::ptr::null_mut();
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
static mut l_main___closed__35_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__35: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__36_value: lean_string_object<10> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 32, 32, 97, 97, 97, 32, 32, 32, 0]};
static mut l_main___closed__36: *mut lean_object = core::ptr::addr_of!(l_main___closed__36_value) as *mut lean_object;
static mut l_main___closed__37_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__37: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__38_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__38: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__39_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__39: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__40_value: lean_string_object<4> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 98, 99, 0]};
static mut l_main___closed__40: *mut lean_object = core::ptr::addr_of!(l_main___closed__40_value) as *mut lean_object;
static mut l_main___closed__41_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__41: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__42_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__42: u8 = 0;
static mut l_main___closed__43_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__43: u8 = 0;
static mut l_main___closed__44_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__44: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__45_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__45: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00showChars_spec__0_spec__0(mut v_s_1_: *mut lean_object) -> *mut lean_object{
let mut v___x_3_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_4_: *mut lean_object = core::ptr::null_mut(); let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); 
v___x_3_ = lean_get_stdout();
v_putStr_4_ = lean_ctor_get(v___x_3_, 4);
lean_inc_ref(v_putStr_4_);
lean_dec_ref(v___x_3_);
v___x_5_ = lean_apply_2(v_putStr_4_, v_s_1_, lean_box(0));
return v___x_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00showChars_spec__0_spec__0___boxed(mut v_s_6_: *mut lean_object, mut v_a_7_: *mut lean_object) -> *mut lean_object{
let mut v_res_8_: *mut lean_object = core::ptr::null_mut(); 
v_res_8_ = l_IO_print___at___00IO_println___at___00showChars_spec__0_spec__0(v_s_6_);
return v_res_8_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00showChars_spec__0(mut v_s_9_: *mut lean_object) -> *mut lean_object{
let mut v___x_11_: u32 = 0; let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); let mut v___x_13_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = 10;
v___x_12_ = lean_string_push(v_s_9_, v___x_11_);
v___x_13_ = l_IO_print___at___00IO_println___at___00showChars_spec__0_spec__0(v___x_12_);
return v___x_13_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00showChars_spec__0___boxed(mut v_s_14_: *mut lean_object, mut v_a_15_: *mut lean_object) -> *mut lean_object{
let mut v_res_16_: *mut lean_object = core::ptr::null_mut(); 
v_res_16_ = l_IO_println___at___00showChars_spec__0(v_s_14_);
return v_res_16_;
}
#[no_mangle] pub unsafe extern "C" fn l_showChars(mut v_x_19_: *mut lean_object, mut v_x_20_: *mut lean_object, mut v_x_21_: *mut lean_object) -> *mut lean_object{
let mut v_zero_23_: *mut lean_object = core::ptr::null_mut(); let mut v_isZero_24_: u8 = 0; let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: u8 = 0; let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: u32 = 0; let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_33_: *mut lean_object = core::ptr::null_mut(); let mut v_one_34_: *mut lean_object = core::ptr::null_mut(); let mut v_n_35_: *mut lean_object = core::ptr::null_mut(); let mut v___x_36_: *mut lean_object = core::ptr::null_mut(); let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_zero_23_ = lean_unsigned_to_nat(0);
v_isZero_24_ = lean_nat_dec_eq(v_x_19_, v_zero_23_);
if v_isZero_24_ == 1 {
lean_dec(v_x_21_);
lean_dec(v_x_19_);
v___x_25_ = lean_box(0);
v___x_26_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
} else {
v___x_27_ = lean_string_utf8_at_end(v_x_20_, v_x_21_);
if v___x_27_ == 0 {
v___x_28_ = l_showChars___closed__0;
v___x_29_ = lean_string_utf8_get(v_x_20_, v_x_21_);
v___x_30_ = l_showChars___closed__1;
v___x_31_ = lean_string_push(v___x_30_, v___x_29_);
v___x_32_ = lean_string_append(v___x_28_, v___x_31_);
lean_dec_ref(v___x_31_);
v___x_33_ = l_IO_println___at___00showChars_spec__0(v___x_32_);
if lean_obj_tag(v___x_33_) == 0 {
lean_dec_ref_known(v___x_33_, 1);
v_one_34_ = lean_unsigned_to_nat(1);
v_n_35_ = lean_nat_sub(v_x_19_, v_one_34_);
lean_dec(v_x_19_);
v___x_36_ = lean_string_utf8_next(v_x_20_, v_x_21_);
lean_dec(v_x_21_);
v_x_19_ = v_n_35_;
v_x_21_ = v___x_36_;
state = 0; continue;
} else {
lean_dec(v_x_21_);
lean_dec(v_x_19_);
return v___x_33_;
}
} else {
lean_dec(v_x_21_);
lean_dec(v_x_19_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_showChars___boxed(mut v_x_40_: *mut lean_object, mut v_x_41_: *mut lean_object, mut v_x_42_: *mut lean_object, mut v_a_43_: *mut lean_object) -> *mut lean_object{
let mut v_res_44_: *mut lean_object = core::ptr::null_mut(); 
v_res_44_ = l_showChars(v_x_40_, v_x_41_, v_x_42_);
lean_dec_ref(v_x_41_);
return v_res_44_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1(mut v_s_47_: u8) -> *mut lean_object{
let mut v___y_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: u32 = 0; let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if v_s_47_ == 0 {
v___x_54_ = l_IO_println___at___00main_spec__1___closed__0;
v___y_50_ = v___x_54_;
state = 1; continue;
} else {
v___x_55_ = l_IO_println___at___00main_spec__1___closed__1;
v___y_50_ = v___x_55_;
state = 1; continue;
}
}
1 => {
v___x_51_ = 10;
lean_inc_ref(v___y_50_);
v___x_52_ = lean_string_push(v___y_50_, v___x_51_);
v___x_53_ = l_IO_print___at___00IO_println___at___00showChars_spec__0_spec__0(v___x_52_);
return v___x_53_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__1___boxed(mut v_s_56_: *mut lean_object, mut v_a_57_: *mut lean_object) -> *mut lean_object{
let mut v_s_boxed_58_: u8 = 0; let mut v_res_59_: *mut lean_object = core::ptr::null_mut(); 
v_s_boxed_58_ = (lean_unbox(v_s_56_) as u8);
v_res_59_ = l_IO_println___at___00main_spec__1(v_s_boxed_58_);
return v_res_59_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2(mut v_s_60_: *mut lean_object) -> *mut lean_object{
let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); let mut v___x_65_: u32 = 0; let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
v___x_62_ = lean_unsigned_to_nat(120);
v___x_63_ = lean_unsigned_to_nat(0);
v___x_64_ = l_Std_Format_pretty(v_s_60_, v___x_62_, v___x_63_, v___x_63_);
v___x_65_ = 10;
v___x_66_ = lean_string_push(v___x_64_, v___x_65_);
v___x_67_ = l_IO_print___at___00IO_println___at___00showChars_spec__0_spec__0(v___x_66_);
return v___x_67_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__2___boxed(mut v_s_68_: *mut lean_object, mut v_a_69_: *mut lean_object) -> *mut lean_object{
let mut v_res_70_: *mut lean_object = core::ptr::null_mut(); 
v_res_70_ = l_IO_println___at___00main_spec__2(v_s_68_);
return v_res_70_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_71_: *mut lean_object) -> *mut lean_object{
let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); let mut v___x_74_: u32 = 0; let mut v___x_75_: *mut lean_object = core::ptr::null_mut(); let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); 
v___x_73_ = l_Nat_reprFast(v_s_71_);
v___x_74_ = 10;
v___x_75_ = lean_string_push(v___x_73_, v___x_74_);
v___x_76_ = l_IO_print___at___00IO_println___at___00showChars_spec__0_spec__0(v___x_75_);
return v___x_76_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_77_: *mut lean_object, mut v_a_78_: *mut lean_object) -> *mut lean_object{
let mut v_res_79_: *mut lean_object = core::ptr::null_mut(); 
v_res_79_ = l_IO_println___at___00main_spec__0(v_s_77_);
return v_res_79_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); 
v___x_82_ = l_main___closed__1;
v___x_83_ = lean_string_utf8_byte_size(v___x_82_);
return v___x_83_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> *mut lean_object{
let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); 
v___x_84_ = l_main___closed__0;
v___x_85_ = lean_string_utf8_byte_size(v___x_84_);
return v___x_85_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> u8{
let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: u8 = 0; 
v___x_86_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_87_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_88_ = lean_nat_dec_le(v___x_87_, v___x_86_);
return v___x_88_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> u8{
let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: u8 = 0; 
v___x_89_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_90_ = lean_unsigned_to_nat(0);
v___x_91_ = l_main___closed__0;
v___x_92_ = l_main___closed__1;
v___x_93_ = lean_string_memcmp(v___x_92_, v___x_91_, v___x_90_, v___x_90_, v___x_89_);
return v___x_93_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8() -> *mut lean_object{
let mut v___x_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); 
v___x_96_ = l_main___closed__7;
v___x_97_ = lean_string_utf8_byte_size(v___x_96_);
return v___x_97_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__9() -> *mut lean_object{
let mut v___x_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); 
v___x_98_ = l_main___closed__6;
v___x_99_ = lean_string_utf8_byte_size(v___x_98_);
return v___x_99_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10() -> u8{
let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v___x_102_: u8 = 0; 
v___x_100_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_101_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_102_ = lean_nat_dec_le(v___x_101_, v___x_100_);
return v___x_102_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__11() -> u8{
let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v___x_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: u8 = 0; 
v___x_103_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_104_ = lean_unsigned_to_nat(0);
v___x_105_ = l_main___closed__6;
v___x_106_ = l_main___closed__7;
v___x_107_ = lean_string_memcmp(v___x_106_, v___x_105_, v___x_104_, v___x_104_, v___x_103_);
return v___x_107_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__13() -> *mut lean_object{
let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); 
v___x_109_ = l_main___closed__12;
v___x_110_ = lean_string_utf8_byte_size(v___x_109_);
return v___x_110_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__14() -> u8{
let mut v___x_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); let mut v___x_113_: u8 = 0; 
v___x_111_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__13), core::ptr::addr_of_mut!(l_main___closed__13_once), _init_l_main___closed__13);
v___x_112_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_113_ = lean_nat_dec_le(v___x_112_, v___x_111_);
return v___x_113_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__15() -> u8{
let mut v___x_114_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v___x_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); let mut v___x_118_: u8 = 0; 
v___x_114_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_115_ = lean_unsigned_to_nat(0);
v___x_116_ = l_main___closed__6;
v___x_117_ = l_main___closed__12;
v___x_118_ = lean_string_memcmp(v___x_117_, v___x_116_, v___x_115_, v___x_115_, v___x_114_);
return v___x_118_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__16() -> *mut lean_object{
let mut v___x_119_: *mut lean_object = core::ptr::null_mut(); let mut v___x_120_: *mut lean_object = core::ptr::null_mut(); 
v___x_119_ = l_showChars___closed__1;
v___x_120_ = lean_string_utf8_byte_size(v___x_119_);
return v___x_120_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__17() -> u8{
let mut v___x_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_122_: u8 = 0; 
v___x_121_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__16), core::ptr::addr_of_mut!(l_main___closed__16_once), _init_l_main___closed__16);
v___x_122_ = lean_nat_dec_le(v___x_121_, v___x_121_);
return v___x_122_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__18() -> u8{
let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); let mut v___x_126_: u8 = 0; 
v___x_123_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__16), core::ptr::addr_of_mut!(l_main___closed__16_once), _init_l_main___closed__16);
v___x_124_ = lean_unsigned_to_nat(0);
v___x_125_ = l_showChars___closed__1;
v___x_126_ = lean_string_memcmp(v___x_125_, v___x_125_, v___x_124_, v___x_124_, v___x_123_);
return v___x_126_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__20() -> *mut lean_object{
let mut v___x_128_: *mut lean_object = core::ptr::null_mut(); let mut v___x_129_: *mut lean_object = core::ptr::null_mut(); 
v___x_128_ = l_main___closed__19;
v___x_129_ = lean_string_utf8_byte_size(v___x_128_);
return v___x_129_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__21() -> u8{
let mut v___x_130_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v___x_132_: u8 = 0; 
v___x_130_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__20), core::ptr::addr_of_mut!(l_main___closed__20_once), _init_l_main___closed__20);
v___x_131_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__16), core::ptr::addr_of_mut!(l_main___closed__16_once), _init_l_main___closed__16);
v___x_132_ = lean_nat_dec_le(v___x_131_, v___x_130_);
return v___x_132_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__22() -> u8{
let mut v___x_133_: *mut lean_object = core::ptr::null_mut(); let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: u8 = 0; 
v___x_133_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__16), core::ptr::addr_of_mut!(l_main___closed__16_once), _init_l_main___closed__16);
v___x_134_ = lean_unsigned_to_nat(0);
v___x_135_ = l_showChars___closed__1;
v___x_136_ = l_main___closed__19;
v___x_137_ = lean_string_memcmp(v___x_136_, v___x_135_, v___x_134_, v___x_134_, v___x_133_);
return v___x_137_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__23() -> u8{
let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: u8 = 0; 
v___x_138_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__20), core::ptr::addr_of_mut!(l_main___closed__20_once), _init_l_main___closed__20);
v___x_139_ = lean_nat_dec_le(v___x_138_, v___x_138_);
return v___x_139_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__24() -> u8{
let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v___x_143_: u8 = 0; 
v___x_140_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__20), core::ptr::addr_of_mut!(l_main___closed__20_once), _init_l_main___closed__20);
v___x_141_ = lean_unsigned_to_nat(0);
v___x_142_ = l_main___closed__19;
v___x_143_ = lean_string_memcmp(v___x_142_, v___x_142_, v___x_141_, v___x_141_, v___x_140_);
return v___x_143_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__26() -> *mut lean_object{
let mut v_s_u2081_145_: *mut lean_object = core::ptr::null_mut(); let mut v_e_146_: *mut lean_object = core::ptr::null_mut(); 
v_s_u2081_145_ = l_main___closed__25;
v_e_146_ = lean_string_utf8_byte_size(v_s_u2081_145_);
return v_e_146_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__28() -> *mut lean_object{
let mut v___x_148_: *mut lean_object = core::ptr::null_mut(); let mut v___x_149_: *mut lean_object = core::ptr::null_mut(); 
v___x_148_ = l_main___closed__27;
v___x_149_ = lean_string_utf8_byte_size(v___x_148_);
return v___x_149_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__29() -> *mut lean_object{
let mut v___x_150_: *mut lean_object = core::ptr::null_mut(); let mut v_e_151_: *mut lean_object = core::ptr::null_mut(); let mut v___x_152_: *mut lean_object = core::ptr::null_mut(); 
v___x_150_ = lean_unsigned_to_nat(1);
v_e_151_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__26), core::ptr::addr_of_mut!(l_main___closed__26_once), _init_l_main___closed__26);
v___x_152_ = lean_nat_sub(v_e_151_, v___x_150_);
return v___x_152_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__30() -> *mut lean_object{
let mut v___x_153_: *mut lean_object = core::ptr::null_mut(); let mut v___x_154_: *mut lean_object = core::ptr::null_mut(); let mut v_s_u2081_155_: *mut lean_object = core::ptr::null_mut(); let mut v___x_156_: *mut lean_object = core::ptr::null_mut(); 
v___x_153_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__29), core::ptr::addr_of_mut!(l_main___closed__29_once), _init_l_main___closed__29);
v___x_154_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__28), core::ptr::addr_of_mut!(l_main___closed__28_once), _init_l_main___closed__28);
v_s_u2081_155_ = l_main___closed__25;
v___x_156_ = lean_string_utf8_extract(v_s_u2081_155_, v___x_154_, v___x_153_);
return v___x_156_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__31() -> *mut lean_object{
let mut v___x_157_: *mut lean_object = core::ptr::null_mut(); let mut v_e_158_: *mut lean_object = core::ptr::null_mut(); let mut v___x_159_: *mut lean_object = core::ptr::null_mut(); 
v___x_157_ = lean_unsigned_to_nat(2);
v_e_158_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__26), core::ptr::addr_of_mut!(l_main___closed__26_once), _init_l_main___closed__26);
v___x_159_ = lean_nat_sub(v_e_158_, v___x_157_);
return v___x_159_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__32() -> *mut lean_object{
let mut v___x_160_: *mut lean_object = core::ptr::null_mut(); let mut v___x_161_: *mut lean_object = core::ptr::null_mut(); let mut v_s_u2081_162_: *mut lean_object = core::ptr::null_mut(); let mut v___x_163_: *mut lean_object = core::ptr::null_mut(); 
v___x_160_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__31), core::ptr::addr_of_mut!(l_main___closed__31_once), _init_l_main___closed__31);
v___x_161_ = lean_unsigned_to_nat(2);
v_s_u2081_162_ = l_main___closed__25;
v___x_163_ = lean_string_utf8_extract(v_s_u2081_162_, v___x_161_, v___x_160_);
return v___x_163_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__33() -> *mut lean_object{
let mut v_e_164_: *mut lean_object = core::ptr::null_mut(); let mut v___x_165_: *mut lean_object = core::ptr::null_mut(); let mut v_s_u2081_166_: *mut lean_object = core::ptr::null_mut(); let mut v___x_167_: *mut lean_object = core::ptr::null_mut(); 
v_e_164_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__26), core::ptr::addr_of_mut!(l_main___closed__26_once), _init_l_main___closed__26);
v___x_165_ = lean_unsigned_to_nat(7);
v_s_u2081_166_ = l_main___closed__25;
v___x_167_ = lean_string_utf8_extract(v_s_u2081_166_, v___x_165_, v_e_164_);
return v___x_167_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__34() -> *mut lean_object{
let mut v_e_168_: *mut lean_object = core::ptr::null_mut(); let mut v___x_169_: *mut lean_object = core::ptr::null_mut(); let mut v_s_u2081_170_: *mut lean_object = core::ptr::null_mut(); let mut v___x_171_: *mut lean_object = core::ptr::null_mut(); 
v_e_168_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__26), core::ptr::addr_of_mut!(l_main___closed__26_once), _init_l_main___closed__26);
v___x_169_ = lean_unsigned_to_nat(8);
v_s_u2081_170_ = l_main___closed__25;
v___x_171_ = lean_string_utf8_extract(v_s_u2081_170_, v___x_169_, v_e_168_);
return v___x_171_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__35() -> *mut lean_object{
let mut v_e_172_: *mut lean_object = core::ptr::null_mut(); let mut v___x_173_: *mut lean_object = core::ptr::null_mut(); 
v_e_172_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__26), core::ptr::addr_of_mut!(l_main___closed__26_once), _init_l_main___closed__26);
v___x_173_ = l_Nat_reprFast(v_e_172_);
return v___x_173_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__37() -> *mut lean_object{
let mut v___x_175_: *mut lean_object = core::ptr::null_mut(); let mut v___x_176_: *mut lean_object = core::ptr::null_mut(); 
v___x_175_ = l_main___closed__36;
v___x_176_ = lean_string_utf8_byte_size(v___x_175_);
return v___x_176_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__38() -> *mut lean_object{
let mut v___x_177_: *mut lean_object = core::ptr::null_mut(); let mut v_b_178_: *mut lean_object = core::ptr::null_mut(); let mut v___x_179_: *mut lean_object = core::ptr::null_mut(); let mut v___x_180_: *mut lean_object = core::ptr::null_mut(); 
v___x_177_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__37), core::ptr::addr_of_mut!(l_main___closed__37_once), _init_l_main___closed__37);
v_b_178_ = lean_unsigned_to_nat(0);
v___x_179_ = l_main___closed__36;
v___x_180_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_b_178_);
lean_ctor_set(v___x_180_, 2, v___x_177_);
return v___x_180_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__39() -> *mut lean_object{
let mut v___x_181_: *mut lean_object = core::ptr::null_mut(); let mut v___x_182_: *mut lean_object = core::ptr::null_mut(); 
v___x_181_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__38), core::ptr::addr_of_mut!(l_main___closed__38_once), _init_l_main___closed__38);
v___x_182_ = l_String_Slice_trimAscii(v___x_181_);
return v___x_182_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__41() -> *mut lean_object{
let mut v___x_184_: *mut lean_object = core::ptr::null_mut(); let mut v___x_185_: *mut lean_object = core::ptr::null_mut(); 
v___x_184_ = l_main___closed__40;
v___x_185_ = lean_string_utf8_byte_size(v___x_184_);
return v___x_185_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__42() -> u8{
let mut v___x_186_: *mut lean_object = core::ptr::null_mut(); let mut v___x_187_: *mut lean_object = core::ptr::null_mut(); let mut v___x_188_: u8 = 0; 
v___x_186_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__20), core::ptr::addr_of_mut!(l_main___closed__20_once), _init_l_main___closed__20);
v___x_187_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__41), core::ptr::addr_of_mut!(l_main___closed__41_once), _init_l_main___closed__41);
v___x_188_ = lean_nat_dec_le(v___x_187_, v___x_186_);
return v___x_188_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__43() -> u8{
let mut v___x_189_: *mut lean_object = core::ptr::null_mut(); let mut v_b_190_: *mut lean_object = core::ptr::null_mut(); let mut v___x_191_: *mut lean_object = core::ptr::null_mut(); let mut v___x_192_: *mut lean_object = core::ptr::null_mut(); let mut v___x_193_: u8 = 0; 
v___x_189_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__41), core::ptr::addr_of_mut!(l_main___closed__41_once), _init_l_main___closed__41);
v_b_190_ = lean_unsigned_to_nat(0);
v___x_191_ = l_main___closed__40;
v___x_192_ = l_main___closed__19;
v___x_193_ = lean_string_memcmp(v___x_192_, v___x_191_, v_b_190_, v_b_190_, v___x_189_);
return v___x_193_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__44() -> *mut lean_object{
let mut v_e_194_: *mut lean_object = core::ptr::null_mut(); let mut v_b_195_: *mut lean_object = core::ptr::null_mut(); let mut v_s_u2081_196_: *mut lean_object = core::ptr::null_mut(); let mut v___x_197_: *mut lean_object = core::ptr::null_mut(); 
v_e_194_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__26), core::ptr::addr_of_mut!(l_main___closed__26_once), _init_l_main___closed__26);
v_b_195_ = lean_unsigned_to_nat(0);
v_s_u2081_196_ = l_main___closed__25;
v___x_197_ = lean_string_utf8_extract(v_s_u2081_196_, v_b_195_, v_e_194_);
return v___x_197_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__45() -> *mut lean_object{
let mut v_e_198_: *mut lean_object = core::ptr::null_mut(); let mut v___x_199_: *mut lean_object = core::ptr::null_mut(); let mut v_s_u2081_200_: *mut lean_object = core::ptr::null_mut(); let mut v___x_201_: *mut lean_object = core::ptr::null_mut(); 
v_e_198_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__26), core::ptr::addr_of_mut!(l_main___closed__26_once), _init_l_main___closed__26);
v___x_199_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__28), core::ptr::addr_of_mut!(l_main___closed__28_once), _init_l_main___closed__28);
v_s_u2081_200_ = l_main___closed__25;
v___x_201_ = lean_string_utf8_extract(v_s_u2081_200_, v___x_199_, v_e_198_);
return v___x_201_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_202_: u32 = 0; let mut v___x_203_: *mut lean_object = core::ptr::null_mut(); 
v___x_202_ = 0;
v___x_203_ = lean_box_uint32(v___x_202_);
return v___x_203_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___y_206_: *mut lean_object = core::ptr::null_mut(); let mut v___x_207_: *mut lean_object = core::ptr::null_mut(); let mut v___x_208_: *mut lean_object = core::ptr::null_mut(); let mut v___x_210_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_211_: u8 = 0; let mut v___x_212_: *mut lean_object = core::ptr::null_mut(); let mut v___x_214_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_215_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_216_: u8 = 0; let mut v_unused_217_: *mut lean_object = core::ptr::null_mut(); let mut v_a_218_: *mut lean_object = core::ptr::null_mut(); let mut v___x_220_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_221_: u8 = 0; let mut v___x_223_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_224_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_225_: u8 = 0; let mut v_a_226_: *mut lean_object = core::ptr::null_mut(); let mut v___x_228_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_229_: u8 = 0; let mut v___x_231_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_232_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_233_: u8 = 0; let mut v___y_235_: *mut lean_object = core::ptr::null_mut(); let mut v___x_236_: u8 = 0; let mut v___x_237_: *mut lean_object = core::ptr::null_mut(); let mut v___x_238_: u8 = 0; let mut v___x_239_: *mut lean_object = core::ptr::null_mut(); let mut v_a_240_: *mut lean_object = core::ptr::null_mut(); let mut v___x_242_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_243_: u8 = 0; let mut v___x_245_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_246_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_247_: u8 = 0; let mut v___y_249_: *mut lean_object = core::ptr::null_mut(); let mut v___x_250_: u8 = 0; let mut v___x_251_: *mut lean_object = core::ptr::null_mut(); let mut v___x_252_: u8 = 0; let mut v___x_253_: *mut lean_object = core::ptr::null_mut(); let mut v_a_254_: *mut lean_object = core::ptr::null_mut(); let mut v___x_256_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_257_: u8 = 0; let mut v___x_259_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_260_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_261_: u8 = 0; let mut v___y_263_: *mut lean_object = core::ptr::null_mut(); let mut v___x_264_: u8 = 0; let mut v___x_265_: *mut lean_object = core::ptr::null_mut(); let mut v___x_266_: u8 = 0; let mut v___x_267_: *mut lean_object = core::ptr::null_mut(); let mut v_a_268_: *mut lean_object = core::ptr::null_mut(); let mut v___x_270_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_271_: u8 = 0; let mut v___x_273_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_274_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_275_: u8 = 0; let mut v___y_277_: *mut lean_object = core::ptr::null_mut(); let mut v___x_278_: u8 = 0; let mut v___x_279_: *mut lean_object = core::ptr::null_mut(); let mut v___x_280_: u8 = 0; let mut v___x_281_: *mut lean_object = core::ptr::null_mut(); let mut v_a_282_: *mut lean_object = core::ptr::null_mut(); let mut v___x_284_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_285_: u8 = 0; let mut v___x_287_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_288_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_289_: u8 = 0; let mut v___y_291_: *mut lean_object = core::ptr::null_mut(); let mut v___x_292_: u8 = 0; let mut v___x_293_: *mut lean_object = core::ptr::null_mut(); let mut v___x_294_: u8 = 0; let mut v___x_295_: *mut lean_object = core::ptr::null_mut(); let mut v_a_296_: *mut lean_object = core::ptr::null_mut(); let mut v___x_298_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_299_: u8 = 0; let mut v___x_301_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_302_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_303_: u8 = 0; let mut v___y_305_: *mut lean_object = core::ptr::null_mut(); let mut v___x_306_: u8 = 0; let mut v___x_307_: *mut lean_object = core::ptr::null_mut(); let mut v___x_308_: u8 = 0; let mut v___x_309_: *mut lean_object = core::ptr::null_mut(); let mut v_a_310_: *mut lean_object = core::ptr::null_mut(); let mut v___x_312_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_313_: u8 = 0; let mut v___x_315_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_316_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_317_: u8 = 0; let mut v_s_u2081_318_: *mut lean_object = core::ptr::null_mut(); let mut v_b_319_: *mut lean_object = core::ptr::null_mut(); let mut v___y_321_: *mut lean_object = core::ptr::null_mut(); let mut v___x_322_: *mut lean_object = core::ptr::null_mut(); let mut v___x_323_: *mut lean_object = core::ptr::null_mut(); let mut v___x_324_: *mut lean_object = core::ptr::null_mut(); let mut v___x_325_: *mut lean_object = core::ptr::null_mut(); let mut v___x_326_: *mut lean_object = core::ptr::null_mut(); let mut v___x_327_: *mut lean_object = core::ptr::null_mut(); let mut v___x_328_: *mut lean_object = core::ptr::null_mut(); let mut v___x_329_: *mut lean_object = core::ptr::null_mut(); let mut v___x_330_: *mut lean_object = core::ptr::null_mut(); let mut v___x_331_: *mut lean_object = core::ptr::null_mut(); let mut v___x_332_: *mut lean_object = core::ptr::null_mut(); let mut v_str_333_: *mut lean_object = core::ptr::null_mut(); let mut v_startInclusive_334_: *mut lean_object = core::ptr::null_mut(); let mut v_endExclusive_335_: *mut lean_object = core::ptr::null_mut(); let mut v___x_336_: *mut lean_object = core::ptr::null_mut(); let mut v___x_337_: *mut lean_object = core::ptr::null_mut(); let mut v___x_338_: *mut lean_object = core::ptr::null_mut(); let mut v___x_339_: *mut lean_object = core::ptr::null_mut(); let mut v___x_340_: *mut lean_object = core::ptr::null_mut(); let mut v___x_341_: *mut lean_object = core::ptr::null_mut(); let mut v___x_342_: u8 = 0; let mut v___x_343_: *mut lean_object = core::ptr::null_mut(); let mut v___x_344_: u8 = 0; let mut v___x_345_: *mut lean_object = core::ptr::null_mut(); let mut v_a_346_: *mut lean_object = core::ptr::null_mut(); let mut v___x_348_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_349_: u8 = 0; let mut v___x_351_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_352_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_353_: u8 = 0; let mut v_a_354_: *mut lean_object = core::ptr::null_mut(); let mut v___x_356_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_357_: u8 = 0; let mut v___x_359_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_360_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_361_: u8 = 0; let mut v_a_362_: *mut lean_object = core::ptr::null_mut(); let mut v___x_364_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_365_: u8 = 0; let mut v___x_367_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_368_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_369_: u8 = 0; let mut v_a_370_: *mut lean_object = core::ptr::null_mut(); let mut v___x_372_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_373_: u8 = 0; let mut v___x_375_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_376_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_377_: u8 = 0; let mut v_a_378_: *mut lean_object = core::ptr::null_mut(); let mut v___x_380_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_381_: u8 = 0; let mut v___x_383_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_384_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_385_: u8 = 0; let mut v_a_386_: *mut lean_object = core::ptr::null_mut(); let mut v___x_388_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_389_: u8 = 0; let mut v___x_391_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_392_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_393_: u8 = 0; let mut v_a_394_: *mut lean_object = core::ptr::null_mut(); let mut v___x_396_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_397_: u8 = 0; let mut v___x_399_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_400_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_401_: u8 = 0; let mut v_a_402_: *mut lean_object = core::ptr::null_mut(); let mut v___x_404_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_405_: u8 = 0; let mut v___x_407_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_408_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_409_: u8 = 0; let mut v___x_410_: *mut lean_object = core::ptr::null_mut(); let mut v___x_411_: *mut lean_object = core::ptr::null_mut(); let mut v___x_412_: *mut lean_object = core::ptr::null_mut(); let mut v___x_413_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v_s_u2081_318_ = l_main___closed__25;
v_b_319_ = lean_unsigned_to_nat(0);
v___x_410_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__44), core::ptr::addr_of_mut!(l_main___closed__44_once), _init_l_main___closed__44);
v___x_411_ = l_IO_println___at___00showChars_spec__0(v___x_410_);
if lean_obj_tag(v___x_411_) == 0 {
lean_dec_ref_known(v___x_411_, 1);
v___x_412_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__45), core::ptr::addr_of_mut!(l_main___closed__45_once), _init_l_main___closed__45);
v___x_413_ = l_IO_println___at___00showChars_spec__0(v___x_412_);
v___y_321_ = v___x_413_;
state = 26; continue;
} else {
v___y_321_ = v___x_411_;
state = 26; continue;
}
}
1 => {
if lean_obj_tag(v___y_206_) == 0 {
lean_dec_ref_known(v___y_206_, 1);
v___x_207_ = lean_unsigned_to_nat(2);
v___x_208_ = l_IO_println___at___00main_spec__0(v___x_207_);
if lean_obj_tag(v___x_208_) == 0 {
v_isSharedCheck_216_ = (!lean_is_exclusive(v___x_208_)) as u8;
if v_isSharedCheck_216_ == 0 {
v_unused_217_ = lean_ctor_get(v___x_208_, 0);
lean_dec(v_unused_217_);
v___x_210_ = v___x_208_;
v_isShared_211_ = v_isSharedCheck_216_;
state = 2; continue;
} else {
lean_dec(v___x_208_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_216_;
state = 2; continue;
}
} else {
v_a_218_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_225_ = (!lean_is_exclusive(v___x_208_)) as u8;
if v_isSharedCheck_225_ == 0 {
v___x_220_ = v___x_208_;
v_isShared_221_ = v_isSharedCheck_225_;
state = 4; continue;
} else {
lean_inc(v_a_218_);
lean_dec(v___x_208_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
state = 4; continue;
}
}
} else {
v_a_226_ = lean_ctor_get(v___y_206_, 0);
v_isSharedCheck_233_ = (!lean_is_exclusive(v___y_206_)) as u8;
if v_isSharedCheck_233_ == 0 {
v___x_228_ = v___y_206_;
v_isShared_229_ = v_isSharedCheck_233_;
state = 6; continue;
} else {
lean_inc(v_a_226_);
lean_dec(v___y_206_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
state = 6; continue;
}
}
}
2 => {
v___x_212_ = l_main___boxed__const__1;
if v_isShared_211_ == 0 {
lean_ctor_set(v___x_210_, 0, v___x_212_);
v___x_214_ = v___x_210_;
state = 3; continue;
} else {
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
state = 3; continue;
}
}
3 => {
return v___x_214_;
}
4 => {
if v_isShared_221_ == 0 {
v___x_223_ = v___x_220_;
state = 5; continue;
} else {
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
state = 5; continue;
}
}
5 => {
return v___x_223_;
}
6 => {
if v_isShared_229_ == 0 {
v___x_231_ = v___x_228_;
state = 7; continue;
} else {
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
state = 7; continue;
}
}
7 => {
return v___x_231_;
}
8 => {
if lean_obj_tag(v___y_235_) == 0 {
lean_dec_ref_known(v___y_235_, 1);
v___x_236_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
if v___x_236_ == 0 {
v___x_237_ = l_IO_println___at___00main_spec__1(v___x_236_);
v___y_206_ = v___x_237_;
state = 1; continue;
} else {
v___x_238_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_239_ = l_IO_println___at___00main_spec__1(v___x_238_);
v___y_206_ = v___x_239_;
state = 1; continue;
}
} else {
v_a_240_ = lean_ctor_get(v___y_235_, 0);
v_isSharedCheck_247_ = (!lean_is_exclusive(v___y_235_)) as u8;
if v_isSharedCheck_247_ == 0 {
v___x_242_ = v___y_235_;
v_isShared_243_ = v_isSharedCheck_247_;
state = 9; continue;
} else {
lean_inc(v_a_240_);
lean_dec(v___y_235_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
state = 9; continue;
}
}
}
9 => {
if v_isShared_243_ == 0 {
v___x_245_ = v___x_242_;
state = 10; continue;
} else {
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
state = 10; continue;
}
}
10 => {
return v___x_245_;
}
11 => {
if lean_obj_tag(v___y_249_) == 0 {
lean_dec_ref_known(v___y_249_, 1);
v___x_250_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
if v___x_250_ == 0 {
v___x_251_ = l_IO_println___at___00main_spec__1(v___x_250_);
v___y_235_ = v___x_251_;
state = 8; continue;
} else {
v___x_252_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v___x_253_ = l_IO_println___at___00main_spec__1(v___x_252_);
v___y_235_ = v___x_253_;
state = 8; continue;
}
} else {
v_a_254_ = lean_ctor_get(v___y_249_, 0);
v_isSharedCheck_261_ = (!lean_is_exclusive(v___y_249_)) as u8;
if v_isSharedCheck_261_ == 0 {
v___x_256_ = v___y_249_;
v_isShared_257_ = v_isSharedCheck_261_;
state = 12; continue;
} else {
lean_inc(v_a_254_);
lean_dec(v___y_249_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
state = 12; continue;
}
}
}
12 => {
if v_isShared_257_ == 0 {
v___x_259_ = v___x_256_;
state = 13; continue;
} else {
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
state = 13; continue;
}
}
13 => {
return v___x_259_;
}
14 => {
if lean_obj_tag(v___y_263_) == 0 {
lean_dec_ref_known(v___y_263_, 1);
v___x_264_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__14), core::ptr::addr_of_mut!(l_main___closed__14_once), _init_l_main___closed__14);
if v___x_264_ == 0 {
v___x_265_ = l_IO_println___at___00main_spec__1(v___x_264_);
v___y_249_ = v___x_265_;
state = 11; continue;
} else {
v___x_266_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__15), core::ptr::addr_of_mut!(l_main___closed__15_once), _init_l_main___closed__15);
v___x_267_ = l_IO_println___at___00main_spec__1(v___x_266_);
v___y_249_ = v___x_267_;
state = 11; continue;
}
} else {
v_a_268_ = lean_ctor_get(v___y_263_, 0);
v_isSharedCheck_275_ = (!lean_is_exclusive(v___y_263_)) as u8;
if v_isSharedCheck_275_ == 0 {
v___x_270_ = v___y_263_;
v_isShared_271_ = v_isSharedCheck_275_;
state = 15; continue;
} else {
lean_inc(v_a_268_);
lean_dec(v___y_263_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
state = 15; continue;
}
}
}
15 => {
if v_isShared_271_ == 0 {
v___x_273_ = v___x_270_;
state = 16; continue;
} else {
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
state = 16; continue;
}
}
16 => {
return v___x_273_;
}
17 => {
if lean_obj_tag(v___y_277_) == 0 {
lean_dec_ref_known(v___y_277_, 1);
v___x_278_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__17), core::ptr::addr_of_mut!(l_main___closed__17_once), _init_l_main___closed__17);
if v___x_278_ == 0 {
v___x_279_ = l_IO_println___at___00main_spec__1(v___x_278_);
v___y_263_ = v___x_279_;
state = 14; continue;
} else {
v___x_280_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__18), core::ptr::addr_of_mut!(l_main___closed__18_once), _init_l_main___closed__18);
v___x_281_ = l_IO_println___at___00main_spec__1(v___x_280_);
v___y_263_ = v___x_281_;
state = 14; continue;
}
} else {
v_a_282_ = lean_ctor_get(v___y_277_, 0);
v_isSharedCheck_289_ = (!lean_is_exclusive(v___y_277_)) as u8;
if v_isSharedCheck_289_ == 0 {
v___x_284_ = v___y_277_;
v_isShared_285_ = v_isSharedCheck_289_;
state = 18; continue;
} else {
lean_inc(v_a_282_);
lean_dec(v___y_277_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
state = 18; continue;
}
}
}
18 => {
if v_isShared_285_ == 0 {
v___x_287_ = v___x_284_;
state = 19; continue;
} else {
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
state = 19; continue;
}
}
19 => {
return v___x_287_;
}
20 => {
if lean_obj_tag(v___y_291_) == 0 {
lean_dec_ref_known(v___y_291_, 1);
v___x_292_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__21), core::ptr::addr_of_mut!(l_main___closed__21_once), _init_l_main___closed__21);
if v___x_292_ == 0 {
v___x_293_ = l_IO_println___at___00main_spec__1(v___x_292_);
v___y_277_ = v___x_293_;
state = 17; continue;
} else {
v___x_294_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__22), core::ptr::addr_of_mut!(l_main___closed__22_once), _init_l_main___closed__22);
v___x_295_ = l_IO_println___at___00main_spec__1(v___x_294_);
v___y_277_ = v___x_295_;
state = 17; continue;
}
} else {
v_a_296_ = lean_ctor_get(v___y_291_, 0);
v_isSharedCheck_303_ = (!lean_is_exclusive(v___y_291_)) as u8;
if v_isSharedCheck_303_ == 0 {
v___x_298_ = v___y_291_;
v_isShared_299_ = v_isSharedCheck_303_;
state = 21; continue;
} else {
lean_inc(v_a_296_);
lean_dec(v___y_291_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
state = 21; continue;
}
}
}
21 => {
if v_isShared_299_ == 0 {
v___x_301_ = v___x_298_;
state = 22; continue;
} else {
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
state = 22; continue;
}
}
22 => {
return v___x_301_;
}
23 => {
if lean_obj_tag(v___y_305_) == 0 {
lean_dec_ref_known(v___y_305_, 1);
v___x_306_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__23), core::ptr::addr_of_mut!(l_main___closed__23_once), _init_l_main___closed__23);
if v___x_306_ == 0 {
v___x_307_ = l_IO_println___at___00main_spec__1(v___x_306_);
v___y_291_ = v___x_307_;
state = 20; continue;
} else {
v___x_308_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__24), core::ptr::addr_of_mut!(l_main___closed__24_once), _init_l_main___closed__24);
v___x_309_ = l_IO_println___at___00main_spec__1(v___x_308_);
v___y_291_ = v___x_309_;
state = 20; continue;
}
} else {
v_a_310_ = lean_ctor_get(v___y_305_, 0);
v_isSharedCheck_317_ = (!lean_is_exclusive(v___y_305_)) as u8;
if v_isSharedCheck_317_ == 0 {
v___x_312_ = v___y_305_;
v_isShared_313_ = v_isSharedCheck_317_;
state = 24; continue;
} else {
lean_inc(v_a_310_);
lean_dec(v___y_305_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
state = 24; continue;
}
}
}
24 => {
if v_isShared_313_ == 0 {
v___x_315_ = v___x_312_;
state = 25; continue;
} else {
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
state = 25; continue;
}
}
25 => {
return v___x_315_;
}
26 => {
if lean_obj_tag(v___y_321_) == 0 {
lean_dec_ref_known(v___y_321_, 1);
v___x_322_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__30), core::ptr::addr_of_mut!(l_main___closed__30_once), _init_l_main___closed__30);
v___x_323_ = l_IO_println___at___00showChars_spec__0(v___x_322_);
if lean_obj_tag(v___x_323_) == 0 {
lean_dec_ref_known(v___x_323_, 1);
v___x_324_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__32), core::ptr::addr_of_mut!(l_main___closed__32_once), _init_l_main___closed__32);
v___x_325_ = l_IO_println___at___00showChars_spec__0(v___x_324_);
if lean_obj_tag(v___x_325_) == 0 {
lean_dec_ref_known(v___x_325_, 1);
v___x_326_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__33), core::ptr::addr_of_mut!(l_main___closed__33_once), _init_l_main___closed__33);
v___x_327_ = l_IO_println___at___00showChars_spec__0(v___x_326_);
if lean_obj_tag(v___x_327_) == 0 {
lean_dec_ref_known(v___x_327_, 1);
v___x_328_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__34), core::ptr::addr_of_mut!(l_main___closed__34_once), _init_l_main___closed__34);
v___x_329_ = l_IO_println___at___00showChars_spec__0(v___x_328_);
if lean_obj_tag(v___x_329_) == 0 {
lean_dec_ref_known(v___x_329_, 1);
v___x_330_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__35), core::ptr::addr_of_mut!(l_main___closed__35_once), _init_l_main___closed__35);
v___x_331_ = l_IO_println___at___00showChars_spec__0(v___x_330_);
if lean_obj_tag(v___x_331_) == 0 {
lean_dec_ref_known(v___x_331_, 1);
v___x_332_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__39), core::ptr::addr_of_mut!(l_main___closed__39_once), _init_l_main___closed__39);
v_str_333_ = lean_ctor_get(v___x_332_, 0);
v_startInclusive_334_ = lean_ctor_get(v___x_332_, 1);
v_endExclusive_335_ = lean_ctor_get(v___x_332_, 2);
v___x_336_ = lean_string_utf8_extract(v_str_333_, v_startInclusive_334_, v_endExclusive_335_);
v___x_337_ = l_String_quote(v___x_336_);
v___x_338_ = lean_alloc_ctor(3, 1, (0) as u32);
lean_ctor_set(v___x_338_, 0, v___x_337_);
v___x_339_ = l_IO_println___at___00main_spec__2(v___x_338_);
if lean_obj_tag(v___x_339_) == 0 {
lean_dec_ref_known(v___x_339_, 1);
v___x_340_ = lean_unsigned_to_nat(15);
v___x_341_ = l_showChars(v___x_340_, v_s_u2081_318_, v_b_319_);
if lean_obj_tag(v___x_341_) == 0 {
lean_dec_ref_known(v___x_341_, 1);
v___x_342_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__42), core::ptr::addr_of_mut!(l_main___closed__42_once), _init_l_main___closed__42);
if v___x_342_ == 0 {
v___x_343_ = l_IO_println___at___00main_spec__1(v___x_342_);
v___y_305_ = v___x_343_;
state = 23; continue;
} else {
v___x_344_ = lean_uint8_once(core::ptr::addr_of_mut!(l_main___closed__43), core::ptr::addr_of_mut!(l_main___closed__43_once), _init_l_main___closed__43);
v___x_345_ = l_IO_println___at___00main_spec__1(v___x_344_);
v___y_305_ = v___x_345_;
state = 23; continue;
}
} else {
v_a_346_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_353_ = (!lean_is_exclusive(v___x_341_)) as u8;
if v_isSharedCheck_353_ == 0 {
v___x_348_ = v___x_341_;
v_isShared_349_ = v_isSharedCheck_353_;
state = 27; continue;
} else {
lean_inc(v_a_346_);
lean_dec(v___x_341_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
state = 27; continue;
}
}
} else {
v_a_354_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_361_ = (!lean_is_exclusive(v___x_339_)) as u8;
if v_isSharedCheck_361_ == 0 {
v___x_356_ = v___x_339_;
v_isShared_357_ = v_isSharedCheck_361_;
state = 29; continue;
} else {
lean_inc(v_a_354_);
lean_dec(v___x_339_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
state = 29; continue;
}
}
} else {
v_a_362_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_369_ = (!lean_is_exclusive(v___x_331_)) as u8;
if v_isSharedCheck_369_ == 0 {
v___x_364_ = v___x_331_;
v_isShared_365_ = v_isSharedCheck_369_;
state = 31; continue;
} else {
lean_inc(v_a_362_);
lean_dec(v___x_331_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
state = 31; continue;
}
}
} else {
v_a_370_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_377_ = (!lean_is_exclusive(v___x_329_)) as u8;
if v_isSharedCheck_377_ == 0 {
v___x_372_ = v___x_329_;
v_isShared_373_ = v_isSharedCheck_377_;
state = 33; continue;
} else {
lean_inc(v_a_370_);
lean_dec(v___x_329_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
state = 33; continue;
}
}
} else {
v_a_378_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_385_ = (!lean_is_exclusive(v___x_327_)) as u8;
if v_isSharedCheck_385_ == 0 {
v___x_380_ = v___x_327_;
v_isShared_381_ = v_isSharedCheck_385_;
state = 35; continue;
} else {
lean_inc(v_a_378_);
lean_dec(v___x_327_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
state = 35; continue;
}
}
} else {
v_a_386_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_393_ = (!lean_is_exclusive(v___x_325_)) as u8;
if v_isSharedCheck_393_ == 0 {
v___x_388_ = v___x_325_;
v_isShared_389_ = v_isSharedCheck_393_;
state = 37; continue;
} else {
lean_inc(v_a_386_);
lean_dec(v___x_325_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
state = 37; continue;
}
}
} else {
v_a_394_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_401_ = (!lean_is_exclusive(v___x_323_)) as u8;
if v_isSharedCheck_401_ == 0 {
v___x_396_ = v___x_323_;
v_isShared_397_ = v_isSharedCheck_401_;
state = 39; continue;
} else {
lean_inc(v_a_394_);
lean_dec(v___x_323_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
state = 39; continue;
}
}
} else {
v_a_402_ = lean_ctor_get(v___y_321_, 0);
v_isSharedCheck_409_ = (!lean_is_exclusive(v___y_321_)) as u8;
if v_isSharedCheck_409_ == 0 {
v___x_404_ = v___y_321_;
v_isShared_405_ = v_isSharedCheck_409_;
state = 41; continue;
} else {
lean_inc(v_a_402_);
lean_dec(v___y_321_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
state = 41; continue;
}
}
}
27 => {
if v_isShared_349_ == 0 {
v___x_351_ = v___x_348_;
state = 28; continue;
} else {
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
state = 28; continue;
}
}
28 => {
return v___x_351_;
}
29 => {
if v_isShared_357_ == 0 {
v___x_359_ = v___x_356_;
state = 30; continue;
} else {
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
state = 30; continue;
}
}
30 => {
return v___x_359_;
}
31 => {
if v_isShared_365_ == 0 {
v___x_367_ = v___x_364_;
state = 32; continue;
} else {
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
state = 32; continue;
}
}
32 => {
return v___x_367_;
}
33 => {
if v_isShared_373_ == 0 {
v___x_375_ = v___x_372_;
state = 34; continue;
} else {
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
state = 34; continue;
}
}
34 => {
return v___x_375_;
}
35 => {
if v_isShared_381_ == 0 {
v___x_383_ = v___x_380_;
state = 36; continue;
} else {
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
state = 36; continue;
}
}
36 => {
return v___x_383_;
}
37 => {
if v_isShared_389_ == 0 {
v___x_391_ = v___x_388_;
state = 38; continue;
} else {
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
state = 38; continue;
}
}
38 => {
return v___x_391_;
}
39 => {
if v_isShared_397_ == 0 {
v___x_399_ = v___x_396_;
state = 40; continue;
} else {
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
state = 40; continue;
}
}
40 => {
return v___x_399_;
}
41 => {
if v_isShared_405_ == 0 {
v___x_407_ = v___x_404_;
state = 42; continue;
} else {
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
state = 42; continue;
}
}
42 => {
return v___x_407_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_414_: *mut lean_object) -> *mut lean_object{
let mut v_res_415_: *mut lean_object = core::ptr::null_mut(); 
v_res_415_ = _lean_main();
return v_res_415_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_str(builtin: u8) -> *mut lean_object {
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
  let res = initialize_str(1 /* builtin */);
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

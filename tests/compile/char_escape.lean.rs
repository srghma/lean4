// Lean compiler output
// Module: char_escape
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Data::String::Defs::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::System::IO::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::Data::UInt::BasicAux::*;
use lean_init::Init::GetElem::*;
use lean_init::Init::Data::ByteArray::Basic::*;
extern "C" {
    fn lean_string_to_utf8(_: *mut lean_object) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
}
pub static l___private_char__escape_0__badString___closed__0_value: lean_string_object<5> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [1, 97, 98, 99, 0]};
static mut l___private_char__escape_0__badString___closed__0: *mut lean_object = core::ptr::addr_of!(l___private_char__escape_0__badString___closed__0_value) as *mut lean_object;
#[used]
#[no_mangle]
pub static mut l___private_char__escape_0__badString: *mut lean_object = core::ptr::addr_of!(l___private_char__escape_0__badString___closed__0_value) as *mut lean_object;
static mut l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__0: *mut lean_object = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__1: *mut lean_object = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__1_value) as *mut lean_object;
static mut l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__0_value: lean_string_object<12> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 101, 110, 103, 116, 104, 32, 32, 32, 61, 32, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__3_value: lean_string_object<12> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 116, 102, 56, 83, 105, 122, 101, 32, 61, 32, 0]};
static mut l_main___closed__3: *mut lean_object = core::ptr::addr_of!(l_main___closed__3_value) as *mut lean_object;
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__6: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__7_value: lean_string_object<15> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 111, 85, 84, 70, 56, 46, 115, 105, 122, 101, 32, 61, 32, 0]};
static mut l_main___closed__7: *mut lean_object = core::ptr::addr_of!(l_main___closed__7_value) as *mut lean_object;
static mut l_main___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__8: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__9: *mut lean_object = core::ptr::null_mut();
pub static l_main___closed__10_value: lean_string_object<7> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [98, 121, 116, 101, 115, 58, 0]};
static mut l_main___closed__10: *mut lean_object = core::ptr::addr_of!(l_main___closed__10_value) as *mut lean_object;
pub static l_main___closed__11_value: lean_string_object<1> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_main___closed__11: *mut lean_object = core::ptr::addr_of!(l_main___closed__11_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00main_spec__1(mut v_s_3_: *mut lean_object) -> *mut lean_object{
let mut v___x_5_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_6_: *mut lean_object = core::ptr::null_mut(); let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); 
v___x_5_ = lean_get_stdout();
v_putStr_6_ = lean_ctor_get(v___x_5_, 4);
lean_inc_ref(v_putStr_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_apply_2(v_putStr_6_, v_s_3_, lean_box(0));
return v___x_7_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00main_spec__1___boxed(mut v_s_8_: *mut lean_object, mut v_a_9_: *mut lean_object) -> *mut lean_object{
let mut v_res_10_: *mut lean_object = core::ptr::null_mut(); 
v_res_10_ = l_IO_print___at___00main_spec__1(v_s_8_);
return v_res_10_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__0() -> *mut lean_object{
let mut v___x_11_: *mut lean_object = core::ptr::null_mut(); let mut v___x_12_: *mut lean_object = core::ptr::null_mut(); 
v___x_11_ = l___private_char__escape_0__badString___closed__0;
v___x_12_ = lean_string_to_utf8(v___x_11_);
return v___x_12_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2() -> *mut lean_object{
let mut v___x_14_: *mut lean_object = core::ptr::null_mut(); let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_14_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__0);
v___x_15_ = lean_byte_array_size(v___x_14_);
return v___x_15_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg(mut v_upperBound_16_: *mut lean_object, mut v_a_17_: *mut lean_object, mut v_b_18_: *mut lean_object) -> *mut lean_object{
let mut v___x_20_: u8 = 0; let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); let mut v___x_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___y_26_: u8 = 0; let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: *mut lean_object = core::ptr::null_mut(); let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); let mut v___x_30_: *mut lean_object = core::ptr::null_mut(); let mut v___x_31_: *mut lean_object = core::ptr::null_mut(); let mut v___x_32_: *mut lean_object = core::ptr::null_mut(); let mut v___x_34_: *mut lean_object = core::ptr::null_mut(); let mut v___x_35_: u8 = 0; let mut v___x_36_: u8 = 0; let mut v___x_37_: *mut lean_object = core::ptr::null_mut(); let mut v___x_38_: *mut lean_object = core::ptr::null_mut(); let mut v___x_39_: u8 = 0; let mut v___x_40_: u8 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_20_ = lean_nat_dec_lt(v_a_17_, v_upperBound_16_);
if v___x_20_ == 0 {
lean_dec(v_a_17_);
v___x_21_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v___x_21_, 0, v_b_18_);
return v___x_21_;
} else {
v___x_22_ = lean_box(0);
v___x_23_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__0);
v___x_24_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__1;
v___x_34_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2);
v___x_35_ = lean_nat_dec_lt(v_a_17_, v___x_34_);
if v___x_35_ == 0 {
v___x_36_ = l_instInhabitedUInt8;
v___x_37_ = lean_box((v___x_36_) as usize);
v___x_38_ = l_outOfBounds___redArg(v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = (lean_unbox(v___x_38_) as u8);
lean_dec(v___x_38_);
v___y_26_ = v___x_39_;
state = 1; continue;
} else {
v___x_40_ = lean_byte_array_fget(v___x_23_, v_a_17_);
v___y_26_ = v___x_40_;
state = 1; continue;
}
}
}
1 => {
v___x_27_ = lean_uint8_to_nat(v___y_26_);
v___x_28_ = l_Nat_reprFast(v___x_27_);
v___x_29_ = lean_string_append(v___x_24_, v___x_28_);
lean_dec_ref(v___x_28_);
v___x_30_ = l_IO_print___at___00main_spec__1(v___x_29_);
if lean_obj_tag(v___x_30_) == 0 {
lean_dec_ref_known(v___x_30_, 1);
v___x_31_ = lean_unsigned_to_nat(1);
v___x_32_ = lean_nat_add(v_a_17_, v___x_31_);
lean_dec(v_a_17_);
v_a_17_ = v___x_32_;
v_b_18_ = v___x_22_;
state = 0; continue;
} else {
lean_dec(v_a_17_);
return v___x_30_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___boxed(mut v_upperBound_41_: *mut lean_object, mut v_a_42_: *mut lean_object, mut v_b_43_: *mut lean_object, mut v___y_44_: *mut lean_object) -> *mut lean_object{
let mut v_res_45_: *mut lean_object = core::ptr::null_mut(); 
v_res_45_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg(v_upperBound_41_, v_a_42_, v_b_43_);
lean_dec(v_upperBound_41_);
return v_res_45_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_46_: *mut lean_object) -> *mut lean_object{
let mut v___x_48_: u32 = 0; let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); 
v___x_48_ = 10;
v___x_49_ = lean_string_push(v_s_46_, v___x_48_);
v___x_50_ = l_IO_print___at___00main_spec__1(v___x_49_);
return v___x_50_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_51_: *mut lean_object, mut v_a_52_: *mut lean_object) -> *mut lean_object{
let mut v_res_53_: *mut lean_object = core::ptr::null_mut(); 
v_res_53_ = l_IO_println___at___00main_spec__0(v_s_51_);
return v_res_53_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); 
v___x_55_ = lean_unsigned_to_nat(4);
v___x_56_ = l_Nat_reprFast(v___x_55_);
return v___x_56_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); 
v___x_57_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_58_ = l_main___closed__0;
v___x_59_ = lean_string_append(v___x_58_, v___x_57_);
return v___x_59_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> *mut lean_object{
let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); 
v___x_61_ = l___private_char__escape_0__badString___closed__0;
v___x_62_ = lean_string_utf8_byte_size(v___x_61_);
return v___x_62_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_63_: *mut lean_object = core::ptr::null_mut(); let mut v___x_64_: *mut lean_object = core::ptr::null_mut(); 
v___x_63_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___x_64_ = l_Nat_reprFast(v___x_63_);
return v___x_64_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> *mut lean_object{
let mut v___x_65_: *mut lean_object = core::ptr::null_mut(); let mut v___x_66_: *mut lean_object = core::ptr::null_mut(); let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
v___x_65_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_66_ = l_main___closed__3;
v___x_67_ = lean_string_append(v___x_66_, v___x_65_);
return v___x_67_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8() -> *mut lean_object{
let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); 
v___x_69_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2);
v___x_70_ = l_Nat_reprFast(v___x_69_);
return v___x_70_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__9() -> *mut lean_object{
let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); let mut v___x_72_: *mut lean_object = core::ptr::null_mut(); let mut v___x_73_: *mut lean_object = core::ptr::null_mut(); 
v___x_71_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_72_ = l_main___closed__7;
v___x_73_ = lean_string_append(v___x_72_, v___x_71_);
return v___x_73_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); 
v___x_77_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_78_ = l_IO_println___at___00main_spec__0(v___x_77_);
if lean_obj_tag(v___x_78_) == 0 {
let mut v___x_79_: *mut lean_object = core::ptr::null_mut(); let mut v___x_80_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_78_, 1);
v___x_79_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v___x_80_ = l_IO_println___at___00main_spec__0(v___x_79_);
if lean_obj_tag(v___x_80_) == 0 {
let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_80_, 1);
v___x_81_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg___closed__2);
v___x_82_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_83_ = l_IO_println___at___00main_spec__0(v___x_82_);
if lean_obj_tag(v___x_83_) == 0 {
let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_83_, 1);
v___x_84_ = l_main___closed__10;
v___x_85_ = l_IO_print___at___00main_spec__1(v___x_84_);
if lean_obj_tag(v___x_85_) == 0 {
let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v___x_88_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_85_, 1);
v___x_86_ = lean_unsigned_to_nat(0);
v___x_87_ = lean_box(0);
v___x_88_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg(v___x_81_, v___x_86_, v___x_87_);
if lean_obj_tag(v___x_88_) == 0 {
let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); 
lean_dec_ref_known(v___x_88_, 1);
v___x_89_ = l_main___closed__11;
v___x_90_ = l_IO_println___at___00main_spec__0(v___x_89_);
return v___x_90_;
} else {
return v___x_88_;
}
} else {
return v___x_85_;
}
} else {
return v___x_83_;
}
} else {
return v___x_80_;
}
} else {
return v___x_78_;
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_91_: *mut lean_object) -> *mut lean_object{
let mut v_res_92_: *mut lean_object = core::ptr::null_mut(); 
v_res_92_ = _lean_main();
return v_res_92_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__2(mut v_upperBound_93_: *mut lean_object, mut v_inst_94_: *mut lean_object, mut v_R_95_: *mut lean_object, mut v_a_96_: *mut lean_object, mut v_b_97_: *mut lean_object, mut v_c_98_: *mut lean_object) -> *mut lean_object{
let mut v___x_100_: *mut lean_object = core::ptr::null_mut(); 
v___x_100_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__2___redArg(v_upperBound_93_, v_a_96_, v_b_97_);
return v___x_100_;
}
#[no_mangle] pub unsafe extern "C" fn l_WellFounded_opaqueFix_u2083___at___00main_spec__2___boxed(mut v_upperBound_101_: *mut lean_object, mut v_inst_102_: *mut lean_object, mut v_R_103_: *mut lean_object, mut v_a_104_: *mut lean_object, mut v_b_105_: *mut lean_object, mut v_c_106_: *mut lean_object, mut v___y_107_: *mut lean_object) -> *mut lean_object{
let mut v_res_108_: *mut lean_object = core::ptr::null_mut(); 
v_res_108_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__2(v_upperBound_101_, v_inst_102_, v_R_103_, v_a_104_, v_b_105_, v_c_106_);
lean_dec(v_upperBound_101_);
return v_res_108_;
}
static mut _G_runtime_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn runtime_initialize_char__escape(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_runtime_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_runtime_initialized = true;
res = runtime_initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn meta_initialize_char__escape(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_meta_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_meta_initialized = true;
res = runtime_initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_char__escape(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = runtime_initialize_char__escape(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
res = meta_initialize_char__escape(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return initialize_char__escape(builtin);
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    return _lean_main();
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = runtime_initialize_char__escape(1 /* builtin */);
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

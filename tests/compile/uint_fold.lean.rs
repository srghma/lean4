// Lean compiler output
// Module: uint_fold
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::UInt::BasicAux::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
#[used]
#[no_mangle]
pub static mut l_foo: u8 = 0;
static mut l_main___closed__0_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__0: u32 = 0;
static mut l_main___closed__1_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__1: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__2_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__2: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__3_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__3: u32 = 0;
static mut l_main___closed__4_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__4: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__5_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__5: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__6_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__6: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__7_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__7: u32 = 0;
static mut l_main___closed__8_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__8: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__9_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__9: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__10_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__10: u32 = 0;
static mut l_main___closed__11_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__11: *mut lean_object = core::ptr::null_mut();
static mut l_main___closed__12_once: lean_once_cell = lean_once_cell { state: 0, lock: 0 };
static mut l_main___closed__12: *mut lean_object = core::ptr::null_mut();
#[used]
#[no_mangle]
pub static mut l_main___boxed__const__1: *mut lean_object = core::ptr::null_mut();
#[no_mangle] pub unsafe extern "C" fn l_h(mut v_x_1_: *mut lean_object) -> u32{
let mut v___x_2_: u32 = 0; 
v___x_2_ = lean_uint32_of_nat(v_x_1_);
return v___x_2_;
}
#[no_mangle] pub unsafe extern "C" fn l_h___boxed(mut v_x_3_: *mut lean_object) -> *mut lean_object{
let mut v_res_4_: u32 = 0; let mut v_r_5_: *mut lean_object = core::ptr::null_mut(); 
v_res_4_ = l_h(v_x_3_);
lean_dec(v_x_3_);
v_r_5_ = lean_box_uint32(v_res_4_);
return v_r_5_;
}
#[no_mangle] pub unsafe extern "C" fn l_f(mut v_x_6_: u32, mut v_y_7_: u32) -> u32{
let mut v_a1_8_: u32 = 0; let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); let mut v___x_10_: *mut lean_object = core::ptr::null_mut(); let mut v_v_11_: *mut lean_object = core::ptr::null_mut(); let mut v_a2_12_: u32 = 0; let mut v_a3_13_: u32 = 0; let mut v___x_14_: u32 = 0; let mut v___x_15_: u32 = 0; let mut v___x_16_: u32 = 0; let mut v___x_17_: u32 = 0; 
v_a1_8_ = 12700;
v___x_9_ = lean_unsigned_to_nat(10);
v___x_10_ = lean_uint32_to_nat(v_x_6_);
v_v_11_ = lean_nat_add(v___x_9_, v___x_10_);
lean_dec(v___x_10_);
v_a2_12_ = lean_uint32_add(v_x_6_, v_a1_8_);
v_a3_13_ = 10;
v___x_14_ = lean_uint32_add(v_y_7_, v_a2_12_);
v___x_15_ = l_h(v_v_11_);
lean_dec(v_v_11_);
v___x_16_ = lean_uint32_add(v___x_14_, v___x_15_);
v___x_17_ = lean_uint32_add(v___x_16_, v_a3_13_);
return v___x_17_;
}
#[no_mangle] pub unsafe extern "C" fn l_f___boxed(mut v_x_18_: *mut lean_object, mut v_y_19_: *mut lean_object) -> *mut lean_object{
let mut v_x_boxed_20_: u32 = 0; let mut v_y_boxed_21_: u32 = 0; let mut v_res_22_: u32 = 0; let mut v_r_23_: *mut lean_object = core::ptr::null_mut(); 
v_x_boxed_20_ = lean_unbox_uint32(v_x_18_);
lean_dec(v_x_18_);
v_y_boxed_21_ = lean_unbox_uint32(v_y_19_);
lean_dec(v_y_19_);
v_res_22_ = l_f(v_x_boxed_20_, v_y_boxed_21_);
v_r_23_ = lean_box_uint32(v_res_22_);
return v_r_23_;
}
#[no_mangle] pub unsafe extern "C" fn l_g(mut v_x_24_: u32, mut v_y_25_: u32) -> u32{
let mut v___x_26_: u32 = 0; let mut v___x_27_: u8 = 0; let mut v___x_28_: u32 = 0; let mut v___x_29_: u32 = 0; let mut v___x_30_: u32 = 0; let mut v___x_31_: u32 = 0; 
let mut state = 0;
loop {
match state {
0 => {
v___x_26_ = 0;
v___x_27_ = lean_uint32_dec_eq(v_x_24_, v___x_26_);
if v___x_27_ == 0 {
v___x_28_ = 1;
v___x_29_ = lean_uint32_sub(v_x_24_, v___x_28_);
v___x_30_ = 2;
v___x_31_ = lean_uint32_add(v_y_25_, v___x_30_);
v_x_24_ = v___x_29_;
v_y_25_ = v___x_31_;
state = 0; continue;
} else {
return v_y_25_;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_g___boxed(mut v_x_33_: *mut lean_object, mut v_y_34_: *mut lean_object) -> *mut lean_object{
let mut v_x_boxed_35_: u32 = 0; let mut v_y_boxed_36_: u32 = 0; let mut v_res_37_: u32 = 0; let mut v_r_38_: *mut lean_object = core::ptr::null_mut(); 
v_x_boxed_35_ = lean_unbox_uint32(v_x_33_);
lean_dec(v_x_33_);
v_y_boxed_36_ = lean_unbox_uint32(v_y_34_);
lean_dec(v_y_34_);
v_res_37_ = l_g(v_x_boxed_35_, v_y_boxed_36_);
v_r_38_ = lean_box_uint32(v_res_37_);
return v_r_38_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_foo() -> u8{
let mut v___x_39_: u8 = 0; 
v___x_39_ = 44;
return v___x_39_;
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
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__0() -> u32{
let mut v___x_56_: u32 = 0; let mut v___x_57_: u32 = 0; let mut v___x_58_: u32 = 0; 
v___x_56_ = 5;
v___x_57_ = 3;
v___x_58_ = l_g(v___x_57_, v___x_56_);
return v___x_58_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__1() -> *mut lean_object{
let mut v___x_59_: u32 = 0; let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); 
v___x_59_ = lean_uint32_once(core::ptr::addr_of_mut!(l_main___closed__0), core::ptr::addr_of_mut!(l_main___closed__0_once), _init_l_main___closed__0);
v___x_60_ = lean_uint32_to_nat(v___x_59_);
return v___x_60_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__2() -> *mut lean_object{
let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); 
v___x_61_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__1), core::ptr::addr_of_mut!(l_main___closed__1_once), _init_l_main___closed__1);
v___x_62_ = l_Nat_reprFast(v___x_61_);
return v___x_62_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__3() -> u32{
let mut v___x_63_: u32 = 0; let mut v___x_64_: u32 = 0; let mut v___x_65_: u32 = 0; 
v___x_63_ = 6;
v___x_64_ = 0;
v___x_65_ = l_g(v___x_64_, v___x_63_);
return v___x_65_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__4() -> *mut lean_object{
let mut v___x_66_: u32 = 0; let mut v___x_67_: *mut lean_object = core::ptr::null_mut(); 
v___x_66_ = lean_uint32_once(core::ptr::addr_of_mut!(l_main___closed__3), core::ptr::addr_of_mut!(l_main___closed__3_once), _init_l_main___closed__3);
v___x_67_ = lean_uint32_to_nat(v___x_66_);
return v___x_67_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__5() -> *mut lean_object{
let mut v___x_68_: *mut lean_object = core::ptr::null_mut(); let mut v___x_69_: *mut lean_object = core::ptr::null_mut(); 
v___x_68_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__4), core::ptr::addr_of_mut!(l_main___closed__4_once), _init_l_main___closed__4);
v___x_69_ = l_Nat_reprFast(v___x_68_);
return v___x_69_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__6() -> *mut lean_object{
let mut v___x_70_: *mut lean_object = core::ptr::null_mut(); let mut v___x_71_: *mut lean_object = core::ptr::null_mut(); 
v___x_70_ = lean_unsigned_to_nat(44);
v___x_71_ = l_Nat_reprFast(v___x_70_);
return v___x_71_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__7() -> u32{
let mut v___x_72_: u32 = 0; let mut v___x_73_: u32 = 0; let mut v___x_74_: u32 = 0; 
v___x_72_ = 20;
v___x_73_ = 10;
v___x_74_ = l_f(v___x_73_, v___x_72_);
return v___x_74_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__8() -> *mut lean_object{
let mut v___x_75_: u32 = 0; let mut v___x_76_: *mut lean_object = core::ptr::null_mut(); 
v___x_75_ = lean_uint32_once(core::ptr::addr_of_mut!(l_main___closed__7), core::ptr::addr_of_mut!(l_main___closed__7_once), _init_l_main___closed__7);
v___x_76_ = lean_uint32_to_nat(v___x_75_);
return v___x_76_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__9() -> *mut lean_object{
let mut v___x_77_: *mut lean_object = core::ptr::null_mut(); let mut v___x_78_: *mut lean_object = core::ptr::null_mut(); 
v___x_77_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__8), core::ptr::addr_of_mut!(l_main___closed__8_once), _init_l_main___closed__8);
v___x_78_ = l_Nat_reprFast(v___x_77_);
return v___x_78_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__10() -> u32{
let mut v___x_79_: u32 = 0; let mut v___x_80_: u32 = 0; 
v___x_79_ = 0;
v___x_80_ = l_f(v___x_79_, v___x_79_);
return v___x_80_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__11() -> *mut lean_object{
let mut v___x_81_: u32 = 0; let mut v___x_82_: *mut lean_object = core::ptr::null_mut(); 
v___x_81_ = lean_uint32_once(core::ptr::addr_of_mut!(l_main___closed__10), core::ptr::addr_of_mut!(l_main___closed__10_once), _init_l_main___closed__10);
v___x_82_ = lean_uint32_to_nat(v___x_81_);
return v___x_82_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___closed__12() -> *mut lean_object{
let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v___x_84_: *mut lean_object = core::ptr::null_mut(); 
v___x_83_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__11), core::ptr::addr_of_mut!(l_main___closed__11_once), _init_l_main___closed__11);
v___x_84_ = l_Nat_reprFast(v___x_83_);
return v___x_84_;
}
#[no_mangle] pub unsafe extern "C" fn _init_l_main___boxed__const__1() -> *mut lean_object{
let mut v___x_85_: u32 = 0; let mut v___x_86_: *mut lean_object = core::ptr::null_mut(); 
v___x_85_ = 0;
v___x_86_ = lean_box_uint32(v___x_85_);
return v___x_86_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main() -> *mut lean_object{
let mut v___y_89_: *mut lean_object = core::ptr::null_mut(); let mut v___x_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v___x_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v___x_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_98_: u8 = 0; let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_102_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_103_: u8 = 0; let mut v_unused_104_: *mut lean_object = core::ptr::null_mut(); let mut v_a_105_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_108_: u8 = 0; let mut v___x_110_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_111_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_112_: u8 = 0; let mut v_a_113_: *mut lean_object = core::ptr::null_mut(); let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_116_: u8 = 0; let mut v___x_118_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_119_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_120_: u8 = 0; let mut v_a_121_: *mut lean_object = core::ptr::null_mut(); let mut v___x_123_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_124_: u8 = 0; let mut v___x_126_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_127_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_128_: u8 = 0; let mut v_a_129_: *mut lean_object = core::ptr::null_mut(); let mut v___x_131_: *mut lean_object = core::ptr::null_mut(); let mut v_isShared_132_: u8 = 0; let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v_reuseFailAlloc_135_: *mut lean_object = core::ptr::null_mut(); let mut v_isSharedCheck_136_: u8 = 0; let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v___x_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
v___x_137_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__9), core::ptr::addr_of_mut!(l_main___closed__9_once), _init_l_main___closed__9);
v___x_138_ = l_IO_println___at___00main_spec__0(v___x_137_);
if lean_obj_tag(v___x_138_) == 0 {
lean_dec_ref_known(v___x_138_, 1);
v___x_139_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__12), core::ptr::addr_of_mut!(l_main___closed__12_once), _init_l_main___closed__12);
v___x_140_ = l_IO_println___at___00main_spec__0(v___x_139_);
v___y_89_ = v___x_140_;
state = 1; continue;
} else {
v___y_89_ = v___x_138_;
state = 1; continue;
}
}
1 => {
if lean_obj_tag(v___y_89_) == 0 {
lean_dec_ref_known(v___y_89_, 1);
v___x_90_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__2), core::ptr::addr_of_mut!(l_main___closed__2_once), _init_l_main___closed__2);
v___x_91_ = l_IO_println___at___00main_spec__0(v___x_90_);
if lean_obj_tag(v___x_91_) == 0 {
lean_dec_ref_known(v___x_91_, 1);
v___x_92_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__5), core::ptr::addr_of_mut!(l_main___closed__5_once), _init_l_main___closed__5);
v___x_93_ = l_IO_println___at___00main_spec__0(v___x_92_);
if lean_obj_tag(v___x_93_) == 0 {
lean_dec_ref_known(v___x_93_, 1);
v___x_94_ = lean_obj_once(core::ptr::addr_of_mut!(l_main___closed__6), core::ptr::addr_of_mut!(l_main___closed__6_once), _init_l_main___closed__6);
v___x_95_ = l_IO_println___at___00main_spec__0(v___x_94_);
if lean_obj_tag(v___x_95_) == 0 {
v_isSharedCheck_103_ = (!lean_is_exclusive(v___x_95_)) as u8;
if v_isSharedCheck_103_ == 0 {
v_unused_104_ = lean_ctor_get(v___x_95_, 0);
lean_dec(v_unused_104_);
v___x_97_ = v___x_95_;
v_isShared_98_ = v_isSharedCheck_103_;
state = 2; continue;
} else {
lean_dec(v___x_95_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_103_;
state = 2; continue;
}
} else {
v_a_105_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_112_ = (!lean_is_exclusive(v___x_95_)) as u8;
if v_isSharedCheck_112_ == 0 {
v___x_107_ = v___x_95_;
v_isShared_108_ = v_isSharedCheck_112_;
state = 4; continue;
} else {
lean_inc(v_a_105_);
lean_dec(v___x_95_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
state = 4; continue;
}
}
} else {
v_a_113_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_120_ = (!lean_is_exclusive(v___x_93_)) as u8;
if v_isSharedCheck_120_ == 0 {
v___x_115_ = v___x_93_;
v_isShared_116_ = v_isSharedCheck_120_;
state = 6; continue;
} else {
lean_inc(v_a_113_);
lean_dec(v___x_93_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
state = 6; continue;
}
}
} else {
v_a_121_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_128_ = (!lean_is_exclusive(v___x_91_)) as u8;
if v_isSharedCheck_128_ == 0 {
v___x_123_ = v___x_91_;
v_isShared_124_ = v_isSharedCheck_128_;
state = 8; continue;
} else {
lean_inc(v_a_121_);
lean_dec(v___x_91_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
state = 8; continue;
}
}
} else {
v_a_129_ = lean_ctor_get(v___y_89_, 0);
v_isSharedCheck_136_ = (!lean_is_exclusive(v___y_89_)) as u8;
if v_isSharedCheck_136_ == 0 {
v___x_131_ = v___y_89_;
v_isShared_132_ = v_isSharedCheck_136_;
state = 10; continue;
} else {
lean_inc(v_a_129_);
lean_dec(v___y_89_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
state = 10; continue;
}
}
}
2 => {
v___x_99_ = l_main___boxed__const__1;
if v_isShared_98_ == 0 {
lean_ctor_set(v___x_97_, 0, v___x_99_);
v___x_101_ = v___x_97_;
state = 3; continue;
} else {
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
state = 3; continue;
}
}
3 => {
return v___x_101_;
}
4 => {
if v_isShared_108_ == 0 {
v___x_110_ = v___x_107_;
state = 5; continue;
} else {
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
state = 5; continue;
}
}
5 => {
return v___x_110_;
}
6 => {
if v_isShared_116_ == 0 {
v___x_118_ = v___x_115_;
state = 7; continue;
} else {
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
state = 7; continue;
}
}
7 => {
return v___x_118_;
}
8 => {
if v_isShared_124_ == 0 {
v___x_126_ = v___x_123_;
state = 9; continue;
} else {
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
state = 9; continue;
}
}
9 => {
return v___x_126_;
}
10 => {
if v_isShared_132_ == 0 {
v___x_134_ = v___x_131_;
state = 11; continue;
} else {
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, (0) as u32);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
state = 11; continue;
}
}
11 => {
return v___x_134_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_a_141_: *mut lean_object) -> *mut lean_object{
let mut v_res_142_: *mut lean_object = core::ptr::null_mut(); 
v_res_142_ = _lean_main();
return v_res_142_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_uint__fold(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
l_foo = _init_l_foo();
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
  let res = initialize_uint__fold(1 /* builtin */);
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

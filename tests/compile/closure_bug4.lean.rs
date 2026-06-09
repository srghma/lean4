// Lean compiler output
// Module: closure_bug4
// Imports: Init Init
use lean_runtime::generated_abi::*;
use lean_init::Init::*;
use lean_init::Init::Prelude::*;
use lean_init::Init::Data::String::Slice::*;
use lean_init::Init::Data::Repr::*;
use lean_init::Init::Data::String::Defs::*;
use lean_init::Init::Data::String::Bootstrap::*;
use lean_init::Init::System::IO::*;
extern "C" {
    fn lean_string_append(_: *mut lean_object, _: *mut lean_object) -> *mut lean_object;
    fn lean_string_push(_: *mut lean_object, _: u32) -> *mut lean_object;
    fn lean_get_stdout() -> *mut lean_object;
}
pub static l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0___closed__0_value) as *mut lean_object;
pub static l_List_toString___at___00f_spec__0___closed__0_value: lean_string_object<3> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_toString___at___00f_spec__0___closed__0: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00f_spec__0___closed__0_value) as *mut lean_object;
pub static l_List_toString___at___00f_spec__0___closed__1_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_toString___at___00f_spec__0___closed__1: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00f_spec__0___closed__1_value) as *mut lean_object;
pub static l_List_toString___at___00f_spec__0___closed__2_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_toString___at___00f_spec__0___closed__2: *mut lean_object = core::ptr::addr_of!(l_List_toString___at___00f_spec__0___closed__2_value) as *mut lean_object;
pub static l_main___closed__0_value: lean_string_object<2> = lean_string_object { m_header: lean_object { m_rc: 0, m_cs_sz: (0) as u16, m_other: 0, m_tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [48, 0]};
static mut l_main___closed__0: *mut lean_object = core::ptr::addr_of!(l_main___closed__0_value) as *mut lean_object;
#[no_mangle] pub unsafe extern "C" fn l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0(mut v_x_2_: *mut lean_object, mut v_x_3_: *mut lean_object) -> *mut lean_object{
let mut v_head_4_: *mut lean_object = core::ptr::null_mut(); let mut v_tail_5_: *mut lean_object = core::ptr::null_mut(); let mut v___x_6_: *mut lean_object = core::ptr::null_mut(); let mut v___x_7_: *mut lean_object = core::ptr::null_mut(); let mut v___x_8_: *mut lean_object = core::ptr::null_mut(); let mut v___x_9_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_x_3_) == 0 {
return v_x_2_;
} else {
v_head_4_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_head_4_);
v_tail_5_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_tail_5_);
lean_dec_ref_known(v_x_3_, 2);
v___x_6_ = l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0___closed__0;
v___x_7_ = lean_string_append(v_x_2_, v___x_6_);
v___x_8_ = l_Nat_reprFast(v_head_4_);
v___x_9_ = lean_string_append(v___x_7_, v___x_8_);
lean_dec_ref(v___x_8_);
v_x_2_ = v___x_9_;
v_x_3_ = v_tail_5_;
state = 0; continue;
}
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_List_toString___at___00f_spec__0(mut v_x_14_: *mut lean_object) -> *mut lean_object{
if lean_obj_tag(v_x_14_) == 0 {
let mut v___x_15_: *mut lean_object = core::ptr::null_mut(); 
v___x_15_ = l_List_toString___at___00f_spec__0___closed__0;
return v___x_15_;
} else {
let mut v_tail_16_: *mut lean_object = core::ptr::null_mut(); 
v_tail_16_ = lean_ctor_get(v_x_14_, 1);
if lean_obj_tag(v_tail_16_) == 0 {
let mut v_head_17_: *mut lean_object = core::ptr::null_mut(); let mut v___x_18_: *mut lean_object = core::ptr::null_mut(); let mut v___x_19_: *mut lean_object = core::ptr::null_mut(); let mut v___x_20_: *mut lean_object = core::ptr::null_mut(); let mut v___x_21_: *mut lean_object = core::ptr::null_mut(); let mut v___x_22_: *mut lean_object = core::ptr::null_mut(); 
v_head_17_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_head_17_);
lean_dec_ref_known(v_x_14_, 2);
v___x_18_ = l_List_toString___at___00f_spec__0___closed__1;
v___x_19_ = l_Nat_reprFast(v_head_17_);
v___x_20_ = lean_string_append(v___x_18_, v___x_19_);
lean_dec_ref(v___x_19_);
v___x_21_ = l_List_toString___at___00f_spec__0___closed__2;
v___x_22_ = lean_string_append(v___x_20_, v___x_21_);
return v___x_22_;
} else {
let mut v_head_23_: *mut lean_object = core::ptr::null_mut(); let mut v___x_24_: *mut lean_object = core::ptr::null_mut(); let mut v___x_25_: *mut lean_object = core::ptr::null_mut(); let mut v___x_26_: *mut lean_object = core::ptr::null_mut(); let mut v___x_27_: *mut lean_object = core::ptr::null_mut(); let mut v___x_28_: u32 = 0; let mut v___x_29_: *mut lean_object = core::ptr::null_mut(); 
lean_inc(v_tail_16_);
v_head_23_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_head_23_);
lean_dec_ref_known(v_x_14_, 2);
v___x_24_ = l_List_toString___at___00f_spec__0___closed__1;
v___x_25_ = l_Nat_reprFast(v_head_23_);
v___x_26_ = lean_string_append(v___x_24_, v___x_25_);
lean_dec_ref(v___x_25_);
v___x_27_ = l_List_foldl___at___00List_toString___at___00f_spec__0_spec__0(v___x_26_, v_tail_16_);
v___x_28_ = 93;
v___x_29_ = lean_string_push(v___x_27_, v___x_28_);
return v___x_29_;
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_f___lam__0(mut v_00x15_30_: *mut lean_object, mut v_00x14_31_: *mut lean_object, mut v_00x13_32_: *mut lean_object, mut v_00x12_33_: *mut lean_object, mut v_00x11_34_: *mut lean_object, mut v_00x10_35_: *mut lean_object, mut v_x9_36_: *mut lean_object, mut v_x8_37_: *mut lean_object, mut v_x7_38_: *mut lean_object, mut v_x6_39_: *mut lean_object, mut v_x5_40_: *mut lean_object, mut v_x4_41_: *mut lean_object, mut v_x3_42_: *mut lean_object, mut v_x2_43_: *mut lean_object, mut v_x1_44_: *mut lean_object, mut v_y_45_: *mut lean_object) -> *mut lean_object{
let mut v___x_46_: *mut lean_object = core::ptr::null_mut(); let mut v___x_47_: *mut lean_object = core::ptr::null_mut(); let mut v___x_48_: *mut lean_object = core::ptr::null_mut(); let mut v___x_49_: *mut lean_object = core::ptr::null_mut(); let mut v___x_50_: *mut lean_object = core::ptr::null_mut(); let mut v___x_51_: *mut lean_object = core::ptr::null_mut(); let mut v___x_52_: *mut lean_object = core::ptr::null_mut(); let mut v___x_53_: *mut lean_object = core::ptr::null_mut(); let mut v___x_54_: *mut lean_object = core::ptr::null_mut(); let mut v___x_55_: *mut lean_object = core::ptr::null_mut(); let mut v___x_56_: *mut lean_object = core::ptr::null_mut(); let mut v___x_57_: *mut lean_object = core::ptr::null_mut(); let mut v___x_58_: *mut lean_object = core::ptr::null_mut(); let mut v___x_59_: *mut lean_object = core::ptr::null_mut(); let mut v___x_60_: *mut lean_object = core::ptr::null_mut(); let mut v___x_61_: *mut lean_object = core::ptr::null_mut(); let mut v___x_62_: *mut lean_object = core::ptr::null_mut(); 
v___x_46_ = lean_box(0);
v___x_47_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_47_, 0, v_00x15_30_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_48_, 0, v_00x14_31_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
v___x_49_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_49_, 0, v_00x13_32_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_50_, 0, v_00x12_33_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_51_, 0, v_00x11_34_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_52_, 0, v_00x10_35_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_53_, 0, v_x9_36_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_54_, 0, v_x8_37_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_55_, 0, v_x7_38_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_56_, 0, v_x6_39_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_57_, 0, v_x5_40_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_58_, 0, v_x4_41_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_59_, 0, v_x3_42_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_60_, 0, v_x2_43_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_alloc_ctor(1, 2, (0) as u32);
lean_ctor_set(v___x_61_, 0, v_x1_44_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = l_List_toString___at___00f_spec__0(v___x_61_);
return v___x_62_;
}
#[no_mangle] pub unsafe extern "C" fn l_f___lam__0___boxed(mut v_00x15_63_: *mut lean_object, mut v_00x14_64_: *mut lean_object, mut v_00x13_65_: *mut lean_object, mut v_00x12_66_: *mut lean_object, mut v_00x11_67_: *mut lean_object, mut v_00x10_68_: *mut lean_object, mut v_x9_69_: *mut lean_object, mut v_x8_70_: *mut lean_object, mut v_x7_71_: *mut lean_object, mut v_x6_72_: *mut lean_object, mut v_x5_73_: *mut lean_object, mut v_x4_74_: *mut lean_object, mut v_x3_75_: *mut lean_object, mut v_x2_76_: *mut lean_object, mut v_x1_77_: *mut lean_object, mut v_y_78_: *mut lean_object) -> *mut lean_object{
let mut v_res_79_: *mut lean_object = core::ptr::null_mut(); 
v_res_79_ = l_f___lam__0(v_00x15_63_, v_00x14_64_, v_00x13_65_, v_00x12_66_, v_00x11_67_, v_00x10_68_, v_x9_69_, v_x8_70_, v_x7_71_, v_x6_72_, v_x5_73_, v_x4_74_, v_x3_75_, v_x2_76_, v_x1_77_, v_y_78_);
lean_dec(v_y_78_);
return v_res_79_;
}
#[no_mangle] pub unsafe extern "C" fn l_f(mut v_x_80_: *mut lean_object) -> *mut lean_object{
let mut v___x_81_: *mut lean_object = core::ptr::null_mut(); let mut v_x1_82_: *mut lean_object = core::ptr::null_mut(); let mut v___x_83_: *mut lean_object = core::ptr::null_mut(); let mut v_x2_84_: *mut lean_object = core::ptr::null_mut(); let mut v___x_85_: *mut lean_object = core::ptr::null_mut(); let mut v_x3_86_: *mut lean_object = core::ptr::null_mut(); let mut v___x_87_: *mut lean_object = core::ptr::null_mut(); let mut v_x4_88_: *mut lean_object = core::ptr::null_mut(); let mut v___x_89_: *mut lean_object = core::ptr::null_mut(); let mut v_x5_90_: *mut lean_object = core::ptr::null_mut(); let mut v___x_91_: *mut lean_object = core::ptr::null_mut(); let mut v_x6_92_: *mut lean_object = core::ptr::null_mut(); let mut v___x_93_: *mut lean_object = core::ptr::null_mut(); let mut v_x7_94_: *mut lean_object = core::ptr::null_mut(); let mut v___x_95_: *mut lean_object = core::ptr::null_mut(); let mut v_x8_96_: *mut lean_object = core::ptr::null_mut(); let mut v___x_97_: *mut lean_object = core::ptr::null_mut(); let mut v_x9_98_: *mut lean_object = core::ptr::null_mut(); let mut v___x_99_: *mut lean_object = core::ptr::null_mut(); let mut v_00x10_100_: *mut lean_object = core::ptr::null_mut(); let mut v___x_101_: *mut lean_object = core::ptr::null_mut(); let mut v_00x11_102_: *mut lean_object = core::ptr::null_mut(); let mut v___x_103_: *mut lean_object = core::ptr::null_mut(); let mut v_00x12_104_: *mut lean_object = core::ptr::null_mut(); let mut v___x_105_: *mut lean_object = core::ptr::null_mut(); let mut v_00x13_106_: *mut lean_object = core::ptr::null_mut(); let mut v___x_107_: *mut lean_object = core::ptr::null_mut(); let mut v_00x14_108_: *mut lean_object = core::ptr::null_mut(); let mut v___x_109_: *mut lean_object = core::ptr::null_mut(); let mut v_00x15_110_: *mut lean_object = core::ptr::null_mut(); let mut v___f_111_: *mut lean_object = core::ptr::null_mut(); let mut v___x_112_: *mut lean_object = core::ptr::null_mut(); 
v___x_81_ = lean_unsigned_to_nat(1);
v_x1_82_ = lean_nat_add(v_x_80_, v___x_81_);
v___x_83_ = lean_unsigned_to_nat(2);
v_x2_84_ = lean_nat_add(v_x_80_, v___x_83_);
v___x_85_ = lean_unsigned_to_nat(3);
v_x3_86_ = lean_nat_add(v_x_80_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(4);
v_x4_88_ = lean_nat_add(v_x_80_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(5);
v_x5_90_ = lean_nat_add(v_x_80_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(6);
v_x6_92_ = lean_nat_add(v_x_80_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(7);
v_x7_94_ = lean_nat_add(v_x_80_, v___x_93_);
v___x_95_ = lean_unsigned_to_nat(8);
v_x8_96_ = lean_nat_add(v_x_80_, v___x_95_);
v___x_97_ = lean_unsigned_to_nat(9);
v_x9_98_ = lean_nat_add(v_x_80_, v___x_97_);
v___x_99_ = lean_unsigned_to_nat(10);
v_00x10_100_ = lean_nat_add(v_x_80_, v___x_99_);
v___x_101_ = lean_unsigned_to_nat(11);
v_00x11_102_ = lean_nat_add(v_x_80_, v___x_101_);
v___x_103_ = lean_unsigned_to_nat(12);
v_00x12_104_ = lean_nat_add(v_x_80_, v___x_103_);
v___x_105_ = lean_unsigned_to_nat(13);
v_00x13_106_ = lean_nat_add(v_x_80_, v___x_105_);
v___x_107_ = lean_unsigned_to_nat(14);
v_00x14_108_ = lean_nat_add(v_x_80_, v___x_107_);
v___x_109_ = lean_unsigned_to_nat(15);
v_00x15_110_ = lean_nat_add(v_x_80_, v___x_109_);
v___f_111_ = lean_alloc_closure(l_f___lam__0___boxed as *mut core::ffi::c_void, 16, 15);
lean_closure_set(v___f_111_, 0, v_00x15_110_);
lean_closure_set(v___f_111_, 1, v_00x14_108_);
lean_closure_set(v___f_111_, 2, v_00x13_106_);
lean_closure_set(v___f_111_, 3, v_00x12_104_);
lean_closure_set(v___f_111_, 4, v_00x11_102_);
lean_closure_set(v___f_111_, 5, v_00x10_100_);
lean_closure_set(v___f_111_, 6, v_x9_98_);
lean_closure_set(v___f_111_, 7, v_x8_96_);
lean_closure_set(v___f_111_, 8, v_x7_94_);
lean_closure_set(v___f_111_, 9, v_x6_92_);
lean_closure_set(v___f_111_, 10, v_x5_90_);
lean_closure_set(v___f_111_, 11, v_x4_88_);
lean_closure_set(v___f_111_, 12, v_x3_86_);
lean_closure_set(v___f_111_, 13, v_x2_84_);
lean_closure_set(v___f_111_, 14, v_x1_82_);
v___x_112_ = lean_alloc_ctor(0, 2, (0) as u32);
lean_ctor_set(v___x_112_, 0, v_x_80_);
lean_ctor_set(v___x_112_, 1, v___f_111_);
return v___x_112_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(mut v_s_113_: *mut lean_object) -> *mut lean_object{
let mut v___x_115_: *mut lean_object = core::ptr::null_mut(); let mut v_putStr_116_: *mut lean_object = core::ptr::null_mut(); let mut v___x_117_: *mut lean_object = core::ptr::null_mut(); 
v___x_115_ = lean_get_stdout();
v_putStr_116_ = lean_ctor_get(v___x_115_, 4);
lean_inc_ref(v_putStr_116_);
lean_dec_ref(v___x_115_);
v___x_117_ = lean_apply_2(v_putStr_116_, v_s_113_, lean_box(0));
return v___x_117_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(mut v_s_118_: *mut lean_object, mut v_a_119_: *mut lean_object) -> *mut lean_object{
let mut v_res_120_: *mut lean_object = core::ptr::null_mut(); 
v_res_120_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v_s_118_);
return v_res_120_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0(mut v_s_121_: *mut lean_object) -> *mut lean_object{
let mut v___x_123_: u32 = 0; let mut v___x_124_: *mut lean_object = core::ptr::null_mut(); let mut v___x_125_: *mut lean_object = core::ptr::null_mut(); 
v___x_123_ = 10;
v___x_124_ = lean_string_push(v_s_121_, v___x_123_);
v___x_125_ = l_IO_print___at___00IO_println___at___00main_spec__0_spec__0(v___x_124_);
return v___x_125_;
}
#[no_mangle] pub unsafe extern "C" fn l_IO_println___at___00main_spec__0___boxed(mut v_s_126_: *mut lean_object, mut v_a_127_: *mut lean_object) -> *mut lean_object{
let mut v_res_128_: *mut lean_object = core::ptr::null_mut(); 
v_res_128_ = l_IO_println___at___00main_spec__0(v_s_126_);
return v_res_128_;
}
#[no_mangle] pub unsafe extern "C" fn _lean_main(mut v_xs_130_: *mut lean_object) -> *mut lean_object{
let mut v___y_133_: *mut lean_object = core::ptr::null_mut(); let mut v___x_134_: *mut lean_object = core::ptr::null_mut(); let mut v___x_135_: *mut lean_object = core::ptr::null_mut(); let mut v___x_136_: *mut lean_object = core::ptr::null_mut(); let mut v___x_137_: *mut lean_object = core::ptr::null_mut(); let mut v___x_138_: *mut lean_object = core::ptr::null_mut(); let mut v_snd_139_: *mut lean_object = core::ptr::null_mut(); let mut v___x_140_: *mut lean_object = core::ptr::null_mut(); let mut v___x_141_: *mut lean_object = core::ptr::null_mut(); let mut v___x_142_: *mut lean_object = core::ptr::null_mut(); let mut v_head_143_: *mut lean_object = core::ptr::null_mut(); 
let mut state = 0;
loop {
match state {
0 => {
if lean_obj_tag(v_xs_130_) == 0 {
v___x_142_ = l_main___closed__0;
v___y_133_ = v___x_142_;
state = 1; continue;
} else {
v_head_143_ = lean_ctor_get(v_xs_130_, 0);
lean_inc(v_head_143_);
lean_dec_ref_known(v_xs_130_, 2);
v___y_133_ = v_head_143_;
state = 1; continue;
}
}
1 => {
v___x_134_ = lean_unsigned_to_nat(0);
v___x_135_ = lean_string_utf8_byte_size(v___y_133_);
v___x_136_ = lean_alloc_ctor(0, 3, (0) as u32);
lean_ctor_set(v___x_136_, 0, v___y_133_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_135_);
v___x_137_ = l_String_Slice_toNat_x21(v___x_136_);
lean_dec_ref_known(v___x_136_, 3);
lean_inc(v___x_137_);
v___x_138_ = l_f(v___x_137_);
v_snd_139_ = lean_ctor_get(v___x_138_, 1);
lean_inc(v_snd_139_);
lean_dec_ref(v___x_138_);
v___x_140_ = lean_apply_1(v_snd_139_, v___x_137_);
v___x_141_ = l_IO_println___at___00main_spec__0(v___x_140_);
return v___x_141_;
}
_ => {}
}
}
}
#[no_mangle] pub unsafe extern "C" fn l_main___boxed(mut v_xs_144_: *mut lean_object, mut v_a_145_: *mut lean_object) -> *mut lean_object{
let mut v_res_146_: *mut lean_object = core::ptr::null_mut(); 
v_res_146_ = _lean_main(v_xs_144_);
return v_res_146_;
}
static mut _G_initialized: bool = false;
#[no_mangle]
pub unsafe extern "C" fn initialize_closure__bug4(builtin: u8) -> *mut lean_object {
let mut res: *mut lean_object = core::ptr::null_mut();
if _G_initialized { return lean_io_result_mk_ok(lean_box(0)); }
_G_initialized = true;
res = initialize_Init(builtin);
if lean_io_result_is_error(res) { return res; }
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
unsafe extern "C" fn run_main(argc: core::ffi::c_int, argv: *mut *mut core::ffi::c_char) -> *mut lean_object {
    let mut args_list = lean_box(0);
            let mut i = argc;
            while i > 1 {
                i -= 1;
                let arg_str = lean_mk_string(*argv.add(i as usize));
                let mut fields = [arg_str, args_list];
                args_list = lean_alloc_ctor(1, 2, 0);
                lean_ctor_set(args_list, 0, arg_str);
                lean_ctor_set(args_list, 1, fields[1]);
            }
            return _lean_main(args_list);
}
#[no_mangle]
pub unsafe extern "C" fn main(argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
  argv = lean_setup_args(argc, argv);
  lean_initialize_runtime_module();
  let res = initialize_closure__bug4(1 /* builtin */);
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
